{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}

module Language.Temporalog.Transformation.Temporal.Compiler
  ( eliminateTemporal
  ) where

import Protolude


import Control.Arrow ((>>>))

import           Data.Functor.Foldable (Base, cata, embed, ana, project)
import           Data.Text (pack)
import qualified Data.Map.Strict as M

import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span, dummySpan)
import           Language.Vanillalog.Generic.Pretty (pp)
import           Language.Vanillalog.Generic.Transformation.Util (Algebra, Coalgebra)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

type CompilerMT = StateT ( ([ AG.PredicateSymbol ], Int)
                         , [ AG.Clause (Const Void) (BOp 'ATemporal) ]
                         )

runCompilerMT :: Monad m
              => CompilerMT m a
              -> [ AG.PredicateSymbol ]
              -> m (a, [ AG.Clause (Const Void) (BOp 'ATemporal) ])
runCompilerMT action predSyms = second snd <$> runStateT action ((predSyms, 1), [ ])

addClause :: Monad m => AG.Clause (Const Void) (BOp 'ATemporal) -> CompilerMT m ()
addClause clause = modify (second (clause :))

freshPredSym :: Monad m => CompilerMT m PredicateSymbol
freshPredSym = do
  (predSyms, ix) <- fst <$> get
  pure $ go predSyms ix
  where
    go predSyms i | candidate <- PredicateSymbol [ "aux" <> pack (show i) ] =
      if candidate `elem` predSyms then go predSyms (i + 1) else candidate

type TimeEnv = M.Map AG.PredicateSymbol Term
type TimeEnvMT = ReaderT TimeEnv

runTimeEnvMT :: Monad m => TimeEnvMT m a -> TimeEnv -> m a
runTimeEnvMT = runReaderT

setClock :: Monad m
         => AG.PredicateSymbol -> Term -> TimeEnvMT m a -> TimeEnvMT m a
setClock predSym time = local (M.insert predSym time)

observeClock :: AG.PredicateSymbol -> ClauseM Term
observeClock predSym = do
  env <- ask
  maybe
    ( lift . lift . lift
    $ Log.scream Nothing (pp predSym <> " is not a key in the time environment.")
    )
    pure
    (predSym `M.lookup` env)

type FreshVarMT = StateT ([ Var ], Int)

runFreshVarMT :: Monad m => [ Var ] -> FreshVarMT m a -> m a
runFreshVarMT vars = (`evalStateT` (vars, 0))

freshVar :: Monad m => FreshVarMT m Var
freshVar = do
  (vars, ix) <- get
  put (vars, ix + 1)
  if var ix `elem` vars
    then freshVar
    else pure $ var ix
  where
  var ix = Var dummySpan ("X" <> pack (show ix))

freshTimeEnv :: MD.Metadata
             -> AG.Clause b c
             -- The following is super ugly. It's time I switch to
             -- algebraic effects.
             -> FreshVarMT (CompilerMT Log.LoggerM) TimeEnv
freshTimeEnv metadata cl@AG.Clause{..} = do
  timePredSyms <- lift . lift $ timePredSymsM
  freshVars <- fmap TVar <$> replicateM (length timePredSyms) freshVar
  pure $ M.fromList $ zip timePredSyms freshVars
  where
  predSyms = map #_predSym (AG.atoms cl :: [ AG.AtomicFormula Term])
  timePredSymsM = concatMap MD.timingPreds
              <$> traverse (`MD.lookupM` metadata) predSyms

type ClauseM = TimeEnvMT (FreshVarMT (CompilerMT Log.LoggerM))

runClauseM :: [ Var ] -> TimeEnv -> ClauseM a -> CompilerMT Log.LoggerM a
runClauseM vars timeEnv action =
  runFreshVarMT vars (runTimeEnvMT action timeEnv)

-- |Assembles a clause
mkClause :: PredicateSymbol                  -- |Name of the predicate to define
         -> [ Term ]                         -- |Argument list
         -> AG.Subgoal (BOp 'ATemporal) Term -- |Body formula
         -> AG.Clause (Const Void) (BOp 'ATemporal)
mkClause headPredSym args body =
  AG.Clause (span body)
    (SAtom (span body)
      (AtomicFormula (span body) headPredSym args)) body

eliminateTemporal :: MD.Metadata
                  -> AG.Program Void HOp (BOp 'Temporal)
                  -> Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
eliminateTemporal metadata program = do
  let predSyms = map #_predSym (AG.atoms program :: [ AG.AtomicFormula Term ])
  (newProgram, newClauses) <- runCompilerMT (goPr program) predSyms
  let newStatements = AG.StSentence . AG.SClause <$> newClauses
  pure (newProgram {AG._statements = AG._statements newProgram <> newStatements})
  where
  goPr :: AG.Program Void HOp (BOp 'Temporal)
       -> CompilerMT Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
  goPr AG.Program{..} = do
    newStatements <- traverse goSt _statements
    pure AG.Program{_statements = newStatements,..}

  goSt :: AG.Statement Void HOp (BOp 'Temporal)
       -> CompilerMT Log.LoggerM (AG.Statement Void (Const Void) (BOp 'ATemporal))
  goSt AG.StSentence{..} =
    (\s -> AG.StSentence{_sentence = s,..}) <$> goSent _sentence
  goSt AG.StDeclaration{..} = absurd _declaration

  goSent :: AG.Sentence HOp (BOp 'Temporal)
         -> CompilerMT Log.LoggerM (AG.Sentence (Const Void) (BOp 'ATemporal))
  goSent AG.SClause{..} = (\cl -> AG.SClause{_clause = cl,..}) <$> goClause _clause

  goClause :: AG.Clause HOp (BOp 'Temporal)
           -> CompilerMT Log.LoggerM (AG.Clause (Const Void) (BOp 'ATemporal))
  goClause cl@AG.Clause{..} = do
    let clauseVars = AG.vars cl

    timeEnv <- runFreshVarMT clauseVars (freshTimeEnv metadata cl)

    runClauseM clauseVars timeEnv $ do
      newHead <- goHead _head
      newBody <- goBody _body
      pure AG.Clause {_head = newHead, _body = newBody,..}

  compileAtom :: AtomicFormula Term -> ClauseM (AtomicFormula Term)
  compileAtom atom = do
    timings <- MD.timingPreds
           <$> (lift . lift . lift) (#_predSym atom `MD.lookupM` metadata)
    timeTerms <- traverse observeClock timings
    pure $ atom {_terms = _terms atom <> timeTerms}

  goHead :: AG.Subgoal HOp Term -> ClauseM (AG.Subgoal (Const Void) Term)
  goHead AG.SAtom{..} =
    (\atom -> AG.SAtom{_atom = atom,..}) <$> compileAtom _atom
  goHead (SHeadJump span child timePredSym time) =
    setClock timePredSym time (goHead child)

  goBody :: AG.Subgoal (BOp 'Temporal) Term
         -> ClauseM (AG.Subgoal (BOp 'ATemporal) Term)
  -- Predicate
  goBody AG.SAtom{..} =
    (\atom -> AG.SAtom{_atom = atom,..}) <$> compileAtom _atom
  -- Logical operators
  goBody (SNeg span c)      = SNeg span  <$> goBody c
  goBody (SConj span c1 c2) = SConj span <$> goBody c1 <*> goBody c2
  goBody (SDogru span)      = pure (SDogru span)
  -- Hybrid operators
  goBody (SBodyJump span child timePredSym time) =
    setClock timePredSym time (goBody child)
  goBody (SBind span timePredSym var child) = do
    timeTerm <- observeClock timePredSym
    newChild <- subst' var timeTerm child
    goBody child
  -- Temporal operators
  goBody (SEX span timePredSym child) = do
    timeTerm <- observeClock timePredSym
    nextTimeTerm <- TVar <$> lift freshVar

    -- Advance the time
    let accAtom = accessibilityAtom timePredSym timeTerm nextTimeTerm

    -- Evaluate the child with advanced time
    newChild <- setClock timePredSym nextTimeTerm (goBody child)

    pure $ SConj span accAtom newChild
  goBody (SEU span timePredSym phi psi) = do
    auxPredSym   <- (lift . lift) freshPredSym
    timeTerm     <- observeClock timePredSym
    nextTimeTerm <- TVar <$> lift freshVar

    phi' <- goBody phi
    psi' <- goBody psi

    let params = TVar <$> vars phi <> vars psi

    let auxAtom = SAtom span
          AtomicFormula{ _span = span
                       , _predSym = auxPredSym
                       , _terms = params
                       }

    -- Generate auxillary clauses
    lift $ lift $ addClause $ mkClause auxPredSym params psi'

    -- If the time term is a variable substitute (advance time), otherwise nop.
    recAuxAtom <- case timeTerm of
       TVar var -> subst' var nextTimeTerm auxAtom
       _        -> pure auxAtom

    let accAtom = accessibilityAtom timePredSym timeTerm nextTimeTerm

    lift $ lift $ addClause $ mkClause auxPredSym params
      (SConj span accAtom (SConj span phi' recAuxAtom))

    -- Compile by calling the auxillary clause
    pure auxAtom

accessibilityAtom :: PredicateSymbol
                  -> Term
                  -> Term
                  -> AG.Subgoal (BOp 'ATemporal) Term
accessibilityAtom predSym now next =
  SAtom dummySpan (AtomicFormula { _span = dummySpan
                                 , _predSym = predSym
                                 , _terms = [now, next]
                                 })

subst' :: Var
       -> Term
       -> Subgoal (BOp a) Term
       -> ClauseM (Subgoal (BOp a) Term)
subst' var term sub =
  case sub of
    AG.SAtom{..} -> pure
      AG.SAtom{_atom = _atom {_terms = substParams var term (_terms _atom)},..}
    SBodyJump span child timePredSym time -> do
      let newTime = if time == TVar var then term else time
      newChild <- subst' var term child
      pure $ SBodyJump span newChild timePredSym newTime
    SBind span timePredSym var' child
      -- No free occurrences of var in this child
      | var == var' -> pure $ SBind span timePredSym var child
      -- Substitution would capture, so alpha rename the Bind expression
      | TVar var'' <- term
      , var' == var'' -> do
        alphaVar <- lift freshVar
        alphaChild <- subst' var' (TVar alphaVar) child
        newChild <- subst' var term alphaChild
        pure $ SBind span timePredSym alphaVar newChild
      -- No risk of capture, continue recursing
      | otherwise -> SBind span timePredSym var <$> subst' var term child
    -- Boring cases:
    s@AG.SNullOp{} -> pure s
    AG.SUnOp{..}   -> (\c -> AG.SUnOp{_child = c,..}) <$> subst' var term _child
    AG.SBinOp{..}  -> (\c1 c2 -> AG.SBinOp{_child1 = c1, _child2 = c2,..})
                  <$> subst' var term _child1
                  <*> subst' var term _child2

substParams :: Var -> Term -> [ Term ] -> [ Term ]
substParams var term = map (\case
  t@(TVar v) -> if v == var then term else t
  t          -> t)
