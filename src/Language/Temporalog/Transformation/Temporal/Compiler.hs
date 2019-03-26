{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}

module Language.Temporalog.Transformation.Temporal.Compiler
  ( eliminateTemporal
  ) where

import Protolude

import Control.Arrow ((>>>))

import           Data.Functor.Foldable (Base, cata, embed, ana, project)
import           Data.List (nub)
import           Data.Text (pack)
import qualified Data.Map.Strict as M

import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span, dummySpan)
import           Language.Vanillalog.Generic.Pretty (pp)
import           Language.Vanillalog.Generic.Transformation.Util (Algebra, Coalgebra)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

eliminateTemporal :: MD.Metadata
                  -> AG.Program Void HOp (BOp 'Temporal)
                  -> Log.LoggerM ( MD.Metadata
                                 , AG.Program Void (Const Void) (BOp 'ATemporal)
                                 )
eliminateTemporal metadata program = do
  let predSyms = map #_predSym (AG.atoms program :: [ AG.AtomicFormula Term ])
  ((newProgram, newPredEnv), newClauses) <- runCompilerMT (goPr program) predSyms

  let newStatements = AG.StSentence . AG.SClause <$> newClauses

  let newMetadata =
        foldr' (uncurry MD.addAtemporal) metadata (M.toList newPredEnv)

  pure
    ( newMetadata
    , newProgram {AG._statements = AG._statements newProgram <> newStatements}
    )
  where
  goPr :: AG.Program Void HOp (BOp 'Temporal)
       -> CompilerMT Log.LoggerM
                     ( AG.Program Void (Const Void) (BOp 'ATemporal)
                     , PredTypeEnv
                     )
  goPr AG.Program{..} = do
    (newStatements, predTypeEnvs) <- unzip <$> traverse goSt _statements
    pure ( AG.Program{_statements = newStatements,..}
         , M.unions predTypeEnvs
         )

  goSt :: AG.Statement Void HOp (BOp 'Temporal)
       -> CompilerMT Log.LoggerM
                     ( AG.Statement Void (Const Void) (BOp 'ATemporal)
                     , PredTypeEnv
                     )
  goSt AG.StSentence{..} =
    first (\s -> AG.StSentence{_sentence = s,..}) <$> goSent _sentence
  goSt AG.StDeclaration{..} = absurd _declaration

  goSent :: AG.Sentence HOp (BOp 'Temporal)
         -> CompilerMT Log.LoggerM
                       ( AG.Sentence (Const Void) (BOp 'ATemporal)
                       , PredTypeEnv
                       )
  goSent sent = do
    let sentVars = AG.vars sent

    timePredicates <- lift $ timePreds metadata sent

    (timeEnv, newTimeVars) <-
      runFreshVarMT sentVars (freshTimeEnv timePredicates)

    runClauseM (sentVars <> newTimeVars) timeEnv $ do
      initTypeEnv metadata sent

      case sent of
        AG.SClause AG.Clause{..} -> do
          newHead <- goHead _head
          newBody <- goBody _body
          pure $ AG.SClause AG.Clause {_head = newHead, _body = newBody,..}
        AG.SFact AG.Fact{..} -> do
          newHead <- goHead _head
          pure $ AG.SFact AG.Fact{_head = newHead,..}
        AG.SQuery AG.Query{..} -> do
          newBody <- goBody _body
          AG.SQuery <$> case _head of
            Nothing -> pure $ AG.Query{_head = Nothing, _body = newBody,..}
            Just _ ->
              lift $ lift $ lift $ lift $ Log.scream (Just $ span sent)
                "There shouldn't be any named queries at this stage."

  compileAtom :: AtomicFormula Term -> ClauseM (AtomicFormula Term)
  compileAtom atom = do
    timings <- MD.timingPreds
           <$> (lift . lift . lift . lift) (#_predSym atom `MD.lookupM` metadata)
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
    newChild <- subst var timeTerm child
    goBody child
  -- Temporal operators
  goBody (SEX span timePredSym phi) = do
    x <- observeClock timePredSym
    y <- TVar <$> freshTypedTimeVar metadata timePredSym

    -- Advance the time
    let accAtom = accessibilityAtom timePredSym x y

    -- Evaluate the child with advanced time
    phi' <- setClock timePredSym y (goBody phi)

    pure $ SConj span accAtom phi'
  goBody (SEU span timePredSym phi psi) = do
    -- Get an axuillary predicate and its de facto atom
    auxPredSym <- (lift . lift . lift) freshPredSym

    x <- observeClock timePredSym
    y <- TVar <$> freshTypedTimeVar metadata timePredSym

    phi' <- goBody phi
    psi' <- goBody psi

    let params = TVar <$> nub (vars phi' <> vars psi')

    let auxAtom = SAtom span
          AtomicFormula{ _span = span
                       , _predSym = auxPredSym
                       , _terms = params
                       }

    addAtomType (AG._atom auxAtom)

    groundingTimeAtom <- timeAtom metadata timePredSym x

    -- Generate auxillary clauses
    lift $ lift $ lift $ addClause $ AG.Clause span auxAtom
      (SConj span groundingTimeAtom psi')

    recAuxAtom <- subst' x y auxAtom

    lift $ lift $ lift $ addClause $ AG.Clause span auxAtom
      (SConj span (accessibilityAtom timePredSym x y)
                  (SConj span recAuxAtom phi'))

    -- Compile by calling the auxillary clause
    pure auxAtom
  goBody (SAF span timePredSym phi) = do
    [aux1PredSym, aux2PredSym]  <- replicateM 2 $ (lift . lift . lift) freshPredSym

    -- x is the time term (maybe not even a variable)
    x <- observeClock timePredSym

    -- auxillary variables used to advance time (among other things)
    [y, z] <- replicateM 2 $ freshTypedTimeVar metadata timePredSym

    phi' <- goBody phi

    -- A subset of parameters for aux1 and aux2
    let params = TVar <$> vars phi

    -- Generate auxillary clauses

    -- Negative path finding aux2:
    let aux2Atom = SAtom span
          AtomicFormula{ _span = span
                       , _predSym = aux2PredSym
                       , _terms = params <> [ TVar z ]
                       }

    addAtomType (AG._atom aux2Atom)

    -- Base case:
    -- Find a point phi doesn't hold
    lift $ lift $ lift $ addClause $ AG.Clause span aux2Atom
      (SConj span (accessibilityAtom timePredSym x (TVar z)) (SNeg span phi'))

    -- Inductive case:
    -- Work backwards to find other points it doesn't hold
    recAux2Atom  <- subst z (TVar y) aux2Atom
    phi'Advanced <- subst' x (TVar y) phi'
    let accAtom2 = accessibilityAtom timePredSym (TVar y) (TVar z)

    lift $ lift $ lift $ addClause $ AG.Clause span aux2Atom
      (SConj span accAtom2
                  (SConj span recAux2Atom
                              (SNeg span phi'Advanced)))

    -- Finding negative paths to the loop
    let aux1Atom = SAtom span
          AtomicFormula{ _span = span
                       , _predSym = aux1PredSym
                       , _terms = params
                       }

    addAtomType (AG._atom aux1Atom)

    -- Base case:
    -- Find a handle on the loop using aux2

    -- We assume (hope) that params already has the time parameter (x)
    -- inside so the second x ties the loop.
    let loopyAux2Atom = SAtom span
          AtomicFormula{ _span = span
                       , _predSym = aux2PredSym
                       , _terms = params <> [ x ]
                       }

    lift $ lift $ lift $ addClause $ AG.Clause span aux1Atom loopyAux2Atom

    -- Inductive case:
    -- Work backwards again but not for loops just for paths that lead to
    -- the loop.

    let accAtom1 = accessibilityAtom timePredSym x (TVar y)

    aux1AtomAdvanced <- subst' x (TVar y) aux1Atom

    lift $ lift $ lift $ addClause $ AG.Clause span aux1Atom
      (SConj span accAtom1
                  (SConj span aux1AtomAdvanced
                              (SNeg span phi')))

    pure $ SNeg span aux1Atom

timeAtom :: MD.Metadata
         -> PredicateSymbol
         -> Term
         -> ClauseM (Subgoal (BOp 'ATemporal) Term)
timeAtom metadata predSym timeVar = do
  wildcard <- freshTypedTimeVar metadata predSym
  pure $ accessibilityAtom predSym timeVar (TVar wildcard)

accessibilityAtom :: PredicateSymbol
                  -> Term
                  -> Term
                  -> AG.Subgoal (BOp 'ATemporal) Term
accessibilityAtom predSym now next =
  SAtom dummySpan (AtomicFormula { _span = dummySpan
                                 , _predSym = predSym
                                 , _terms = [now, next]
                                 })

-- |A substitution that allows a constant to be the thing to be replaced.
-- It simply ignores it.
subst' :: Term
       -> Term
       -> Subgoal (BOp a) Term
       -> ClauseM (Subgoal (BOp a) Term)
subst' key val exp =
  case key of
    TVar v -> subst v val exp
    _      -> pure exp

subst :: Var
      -> Term
      -> Subgoal (BOp a) Term
      -> ClauseM (Subgoal (BOp a) Term)
subst var term sub =
  case sub of
    AG.SAtom{..} -> pure
      AG.SAtom{_atom = _atom {_terms = substParams var term (_terms _atom)},..}
    SBodyJump span child timePredSym time -> do
      let newTime = if time == TVar var then term else time
      newChild <- subst var term child
      pure $ SBodyJump span newChild timePredSym newTime
    SBind span timePredSym var' child
      -- No free occurrences of var in this child
      | var == var' -> pure $ SBind span timePredSym var child
      -- Substitution would capture, so alpha rename the Bind expression
      | TVar var'' <- term
      , var' == var'' -> do
        alphaVar <- (lift . lift) freshVar
        alphaChild <- subst var' (TVar alphaVar) child
        newChild <- subst var term alphaChild
        pure $ SBind span timePredSym alphaVar newChild
      -- No risk of capture, continue recursing
      | otherwise -> SBind span timePredSym var <$> subst var term child
    -- Boring cases:
    s@AG.SNullOp{} -> pure s
    AG.SUnOp{..}   -> (\c -> AG.SUnOp{_child = c,..}) <$> subst var term _child
    AG.SBinOp{..}  -> (\c1 c2 -> AG.SBinOp{_child1 = c1, _child2 = c2,..})
                  <$> subst var term _child1
                  <*> subst var term _child2

substParams :: Var -> Term -> [ Term ] -> [ Term ]
substParams var term = map (\case
  t@(TVar v) -> if v == var then term else t
  t          -> t)

--------------------------------------------------------------------------------
-- Necessary effects
--------------------------------------------------------------------------------

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
  modify (first (second (+ 1)))
  pure $ go predSyms ix
  where
    go predSyms i | candidate <- PredicateSymbol [ "aux" <> pack (show i) ] =
      if candidate `elem` predSyms then go predSyms (i + 1) else candidate

type TimeEnv = M.Map AG.PredicateSymbol Term
type TimeEnvMT = ReaderT TimeEnv

runTimeEnvMT :: Monad m => TimeEnvMT m a -> TimeEnv -> m a
runTimeEnvMT = runReaderT

getTimeEnv :: Monad m => TimeEnvMT m TimeEnv
getTimeEnv = ask

setClock :: Monad m
         => AG.PredicateSymbol -> Term -> TimeEnvMT m a -> TimeEnvMT m a
setClock predSym time = local (M.insert predSym time)

observeClock :: AG.PredicateSymbol -> ClauseM Term
observeClock predSym = do
  env <- ask
  maybe
    ( lift . lift . lift . lift
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

freshTimeEnv :: [ AG.PredicateSymbol ]
             -- The following is super ugly. It's time I switch to
             -- algebraic effects.
             -> FreshVarMT (CompilerMT Log.LoggerM)
                  ( TimeEnv
                  , [ Var ] -- Newly generated vars
                  )
freshTimeEnv timePreds = do
  freshVars <- replicateM (length timePreds) freshVar
  pure (M.fromList $ zip timePreds (TVar <$> freshVars), freshVars)

timePreds :: MD.Metadata -> Sentence -> Log.LoggerM [ AG.PredicateSymbol ]
timePreds metadata sent =
  case sent of
    AG.SClause AG.Clause{..} ->
      (<>) <$> headTimePreds _head <*> bodyTimePreds _body
    AG.SQuery  AG.Query{..}  -> bodyTimePreds _body
    AG.SFact   AG.Fact{..}   -> headTimePreds _head

  where
  headTimePreds :: Subgoal HOp Term -> Log.LoggerM [ AG.PredicateSymbol ]
  headTimePreds AG.SAtom{..} = atomTimePreds _atom
  headTimePreds (SHeadJump _ phi predSym _) = (predSym :) <$> headTimePreds phi

  bodyTimePreds :: Subgoal (BOp 'Temporal) Term
                -> Log.LoggerM [ AG.PredicateSymbol ]
  bodyTimePreds AG.SAtom{..} = atomTimePreds _atom
  bodyTimePreds (SBodyJump _ phi timePred _) =
    (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SBind _ timePred _ phi) = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SEX _ timePred phi)     = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SAX _ timePred phi)     = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SEF _ timePred phi)     = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SAF _ timePred phi)     = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SEG _ timePred phi)     = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SAG _ timePred phi)     = (timePred :) <$> bodyTimePreds phi
  bodyTimePreds (SEU _ timePred phi psi) =
    (\xs ys -> timePred : xs <> ys) <$> bodyTimePreds phi <*> bodyTimePreds psi
  bodyTimePreds (SAU _ timePred phi psi) =
    (\xs ys -> timePred : xs <> ys) <$> bodyTimePreds phi <*> bodyTimePreds psi
  bodyTimePreds AG.SNullOp{}  = pure []
  bodyTimePreds AG.SUnOp{..}  = bodyTimePreds _child
  bodyTimePreds AG.SBinOp{..} = (<>) <$> bodyTimePreds _child1
                                     <*> bodyTimePreds _child2

  atomTimePreds :: AtomicFormula Term -> Log.LoggerM [ AG.PredicateSymbol ]
  atomTimePreds AtomicFormula{..} =
    MD.timingPreds <$> _predSym `MD.lookupM` metadata

type VarTypeEnv  = M.Map Var                TermType
type PredTypeEnv = M.Map AG.PredicateSymbol [ TermType ]

type TypeEnv = (VarTypeEnv, PredTypeEnv)

type TypeEnvMT = StateT TypeEnv

runTypeEnvMT :: Monad m => TypeEnvMT m a -> m (a, PredTypeEnv)
runTypeEnvMT action = second snd <$> runStateT action (M.empty, M.empty)

addAtomType :: AG.AtomicFormula Term -> ClauseM ()
addAtomType AG.AtomicFormula{..} = do
  types <- (`traverse` _terms) $ \case
    TVar v -> do
      mType <- lift $ getType v
      maybe
        (lift . lift . lift . lift $ Log.scream (Just _span) $
          "Type of " <> pp v <> " is unknown.") pure mType
    TSym s -> pure $ AG.termType s

  lift $ modify (second (M.insert _predSym types))

getType :: Monad m => Var -> TypeEnvMT m (Maybe TermType)
getType var = M.lookup var . fst <$> get

addVarType :: Var -> TermType -> ClauseM ()
addVarType var termType = do
  mType <- lift $ getType var
  case mType of
    Just termType'
      | termType == termType -> pure ()
      | otherwise -> lift . lift . lift . lift $ Log.scream Nothing $
        "Variable " <> pp var <> " cannot have two types: " <>
        pp termType <> " and " <> pp termType'
    Nothing -> lift $ modify (first (M.insert var termType))

addTimeVarType :: MD.Metadata -> Var -> AG.PredicateSymbol -> ClauseM ()
addTimeVarType metadata var timePredSym = do
  predInfo <- lift . lift . lift . lift $ timePredSym `MD.lookupM` metadata
  case MD.typ predInfo of
    [ termType, _ ] -> addVarType var termType
    ts              -> lift . lift . lift . lift $
      Log.scream (Just $ span var) "Time predicate does not has arity 2."

freshTypedTimeVar :: MD.Metadata -> AG.PredicateSymbol -> ClauseM Var
freshTypedTimeVar metadata timePredSym = do
  var <- lift $ lift freshVar
  addTimeVarType metadata var timePredSym
  pure var

initTypeEnv :: MD.Metadata -> AG.Sentence a b -> ClauseM ()
initTypeEnv metadata sentence = do
  let atoms = AG.atoms sentence
  forM_ atoms $ \AtomicFormula{..} -> do
    predInfo <- lift . lift . lift . lift $ _predSym `MD.lookupM` metadata
    let varsTypes = (`mapMaybe` zip _terms (MD.typ predInfo)) $ \case
          (TVar var, termType) -> Just (var,termType)
          _                    -> Nothing
    traverse (uncurry addVarType) varsTypes

  timeEnv <- getTimeEnv
  forM_ (M.toList timeEnv) $ \(timePredSym, term) ->
    case term of
      TVar var -> addTimeVarType metadata var timePredSym
      _        -> lift . lift . lift . lift $
        Log.scream (Just $ span sentence)
          "Initial time environment contains a non-var."

type ClauseM = TimeEnvMT (TypeEnvMT (FreshVarMT (CompilerMT Log.LoggerM)))

runClauseM :: [ Var ]
           -> TimeEnv
           -> ClauseM a
           -> CompilerMT Log.LoggerM (a, PredTypeEnv)
runClauseM vars timeEnv action =
  runFreshVarMT vars (runTypeEnvMT (runTimeEnvMT action timeEnv))
