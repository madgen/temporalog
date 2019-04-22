{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Temporalog.Transformation.Temporal.Compiler
  ( eliminateTemporal
  ) where

import Protolude

import           Data.String (fromString)
import           Data.List (nub)
import           Data.Text (pack)
import qualified Data.Map.Strict as M

import qualified Language.Exalog.Logger as Log
import           Language.Exalog.SrcLoc (span, dummySpan)

import qualified Language.Vanillalog.Generic.AST as AG
import           Language.Vanillalog.Generic.Pretty (pp)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

eliminateTemporal :: MD.Metadata
                  -> AG.Program Void HOp (BOp 'Temporal)
                  -> Log.Logger ( MD.Metadata
                                 , AG.Program Void (Const Void) (BOp 'ATemporal)
                                 )
eliminateTemporal metadata program = do
  let predSyms = map #_predSym (AG.atoms program :: [ AG.AtomicFormula Term ])
  ((newProgram, newPredEnv), newClauses) <- runCompilerMT (goPr program) predSyms

  let newStatements = AG.StSentence . AG.SClause <$> newClauses

  let newMetadata = foldr' (uncurry MD.addAuxillaryAtemporalPred)
                           metadata
                           (M.toList newPredEnv)

  pure
    ( newMetadata
    , newProgram {AG._statements = AG._statements newProgram <> newStatements}
    )
  where
  goPr :: AG.Program Void HOp (BOp 'Temporal)
       -> CompilerMT Log.Logger
                     ( AG.Program Void (Const Void) (BOp 'ATemporal)
                     , PredTypeEnv
                     )
  goPr AG.Program{..} = do
    (newStatements, predTypeEnvs) <- unzip <$> traverse goSt _statements
    pure ( AG.Program{_statements = newStatements,..}
         , M.unions predTypeEnvs
         )

  goSt :: AG.Statement Void HOp (BOp 'Temporal)
       -> CompilerMT Log.Logger
                     ( AG.Statement Void (Const Void) (BOp 'ATemporal)
                     , PredTypeEnv
                     )
  goSt AG.StSentence{..} =
    first (\s -> AG.StSentence{_sentence = s,..}) <$> goSent _sentence
  goSt AG.StDeclaration{..} = absurd _declaration

  goSent :: AG.Sentence HOp (BOp 'Temporal)
         -> CompilerMT Log.Logger
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
  goHead (SHeadJump _ child timePredSym time) =
    setClock timePredSym time (goHead child)

  goBody :: AG.Subgoal (BOp 'Temporal) Term
         -> ClauseM (AG.Subgoal (BOp 'ATemporal) Term)
  -- Predicate
  goBody AG.SAtom{..} =
    (\atom -> AG.SAtom{_atom = atom,..}) <$> compileAtom _atom
  -- Logical operators
  goBody (SNeg   s c)     = SNeg  s <$> goBody c
  goBody (SConj  s c1 c2) = SConj s <$> goBody c1 <*> goBody c2
  goBody (SDisj  s c1 c2) = SDisj s <$> goBody c1 <*> goBody c2
  goBody (SDogru s)       = pure (SDogru s)
  -- Hybrid operators
  goBody (SBodyJump _ child timePredSym time) =
    setClock timePredSym time (goBody child)
  goBody (SBind _ timePredSym var child) = do
    timeTerm <- observeClock timePredSym
    newChild <- subst var timeTerm child
    goBody newChild
  -- Temporal operators
  goBody rho@(SEX span timePredSym phi) = do
    -- Get an axuillary predicate and its de facto atom
    auxPredSym <- (lift . lift . lift) freshPredSym

    x <- TVar <$> freshTypedTimeVar metadata timePredSym

    let deltaFV = TVar <$> nub (freeVars phi)

    uniqTimePreds <- lift $ lift $ lift $ lift $ uniqTimePredsM metadata rho

    delta <- traverse observeClock uniqTimePreds

    t <- observeClock timePredSym

    -- Transition atom
    let transitionAtom = accessibilityAtom timePredSym t x

    -- Evaluate the child with advanced time
    phi' <- setClock timePredSym x (goBody phi)

    -- Auxillary clause:

    -- Head of the auxillary clause
    let auxAtom =
         AtomicFormula { _span = span , _predSym = auxPredSym , _terms = [] }

    let auxHead = SAtom span (auxAtom {_terms = deltaFV <> delta })

    addAtomType (AG._atom auxHead)

    lift $ lift $ lift $ addClause $ AG.Clause span auxHead
      (SConj span transitionAtom phi')

    pure auxHead
  goBody rho@(SEU span timePredSym phi psi) = do
    -- Get an axuillary predicate and its de facto atom
    auxPredSym <- (lift . lift . lift) freshPredSym

    [ x, y ] <- replicateM 2 $ TVar <$> freshTypedTimeVar metadata timePredSym

    let deltaFV = TVar <$> nub (freeVars rho)

    uniqTimePreds <- lift $ lift $ lift $ lift $ uniqTimePredsM metadata rho

    let timeTermsM = traverse observeClock uniqTimePreds

    delta <- timeTermsM
    deltaX <- setClock timePredSym x timeTermsM
    deltaY <- setClock timePredSym y timeTermsM

    -- Compile subformulae
    phi' <- setClock timePredSym x $ goBody phi
    psi' <- setClock timePredSym x $ goBody psi

    let auxAtom =
         AtomicFormula { _span = span , _predSym = auxPredSym , _terms = [] }

    -- Generate auxillary clauses
    let auxHead = SAtom span (auxAtom {_terms = deltaFV <> deltaX })

    addAtomType (AG._atom auxHead)

    -- Base base:
    lift $ lift $ lift $ addClause $ AG.Clause span auxHead psi'

    -- Inductive clause:
    let auxAtomRec = SAtom span (auxAtom {_terms = deltaFV <> deltaY })

    lift $ lift $ lift $ addClause $ AG.Clause span auxHead
      (SConj span (accessibilityAtom timePredSym x y)
                  (SConj span auxAtomRec phi'))

    -- Compile by calling the auxillary clause
    let auxResult = SAtom span (auxAtom {_terms = deltaFV <> delta })

    pure auxResult
  goBody rho@(SEG span timePredSym phi) = do
    [ aux1PredSym, aux2PredSym ]  <-
      replicateM 2 $ (lift . lift . lift) freshPredSym

    -- auxillary variables used to advance time (among other things)
    [x, y, z] <- replicateM 3 $ TVar <$> freshTypedTimeVar metadata timePredSym

    -- Time parameters
    let deltaFV = TVar <$> nub (freeVars rho)

    let delta   = TVar <$> nub (freeVars rho)

    uniqTimePreds <- lift $ lift $ lift $ lift $ uniqTimePredsM metadata rho

    let timeTermsM = traverse observeClock uniqTimePreds

    delta <- timeTermsM
    deltaX <- setClock timePredSym x timeTermsM
    deltaY <- setClock timePredSym y timeTermsM

    -- Compile the child
    phi' <- setClock timePredSym y (goBody phi)

    let aux2Atom =
         AtomicFormula {_span = span , _predSym = aux2PredSym , _terms = []}

    -- Generate auxillary clauses

    -- AUX2: Negative path finding:
    let aux2BaseHead = SAtom span $
          aux2Atom {_terms = deltaFV <> deltaX <> [ y ] }

    addAtomType (AG._atom aux2BaseHead)

    -- Base case:
    -- Find a point phi doesn't hold
    let acc2 = accessibilityAtom timePredSym x y

    lift $ lift $ lift $ addClause $ AG.Clause span aux2BaseHead
      (SConj span acc2 phi')

    -- Inductive case:
    -- Work backwards to find other points it doesn't hold

    let aux2InductiveHead = SAtom span $ aux2Atom {_terms = deltaFV <> deltaX <> [ z ]}
    let aux2InductiveRec  = SAtom span $ aux2Atom {_terms = deltaFV <> deltaY <> [ z ]}

    lift $ lift $ lift $ addClause $ AG.Clause span aux2InductiveHead
      (SConj span acc2 (SConj span aux2InductiveRec phi'))

    -- AUX1: Finding negative paths to the loop
    let aux1Atom =
         AtomicFormula { _span = span , _predSym = aux1PredSym , _terms = [] }

    let aux1Head = SAtom span $ aux1Atom {_terms = deltaFV <> deltaY}

    addAtomType (AG._atom aux1Head)

    -- Base case:
    -- Find a handle on the loop using aux2

    let loopyAux2Atom = SAtom span $ aux2Atom {_terms = deltaFV <> deltaY <> [ y ]}

    lift $ lift $ lift $ addClause $ AG.Clause span aux1Head loopyAux2Atom

    -- Inductive case:
    -- Work backwards again but not for loops just for paths that lead to
    -- the loop.

    let acc1 = accessibilityAtom timePredSym y x

    let aux1Rec = SAtom span $ aux1Atom {_terms = deltaFV <> deltaX}

    lift $ lift $ lift $ addClause $ AG.Clause span aux1Head
      (SConj span acc1 (SConj span aux1Rec phi'))

    -- Compile by calling the auxillary clause
    let auxResult = SAtom span (aux1Atom {_terms = deltaFV <> delta})

    pure auxResult

accessibilityAtom :: PredicateSymbol
                  -> Term
                  -> Term
                  -> AG.Subgoal (BOp 'ATemporal) Term
accessibilityAtom predSym now next =
  SAtom dummySpan (AtomicFormula { _span = dummySpan
                                 , _predSym = predSym
                                 , _terms = [now, next]
                                 })

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

type CompilerMT = StateT ( ([ PredicateSymbol ], Int)
                         , [ AG.Clause (Const Void) (BOp 'ATemporal) ]
                         )

runCompilerMT :: Monad m
              => CompilerMT m a
              -> [ PredicateSymbol ]
              -> m (a, [ AG.Clause (Const Void) (BOp 'ATemporal) ])
runCompilerMT action predSyms = second snd <$> runStateT action ((predSyms, 1), [ ])

addClause :: Monad m => AG.Clause (Const Void) (BOp 'ATemporal) -> CompilerMT m ()
addClause clause = modify (second (clause :))

freshPredSym :: Monad m => CompilerMT m PredicateSymbol
freshPredSym = do
  (predSyms, ix) <- fst <$> get
  modify (first (second (+ 1)))

  let candidate = PredicateSymbol . fromString $ "aux" <> show ix

  if candidate `elem` predSyms
    then freshPredSym
    else pure candidate

type TimeEnv = M.Map PredicateSymbol Term
type TimeEnvMT = ReaderT TimeEnv

runTimeEnvMT :: Monad m => TimeEnvMT m a -> TimeEnv -> m a
runTimeEnvMT = runReaderT

getTimeEnv :: Monad m => TimeEnvMT m TimeEnv
getTimeEnv = ask

setClock :: Monad m => PredicateSymbol -> Term -> TimeEnvMT m a -> TimeEnvMT m a
setClock predSym time = local (M.insert predSym time)

observeClock :: PredicateSymbol -> ClauseM Term
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

freshTimeEnv :: [ PredicateSymbol ]
             -- The following is super ugly. It's time I switch to
             -- algebraic effects.
             -> FreshVarMT (CompilerMT Log.Logger)
                  ( TimeEnv
                  , [ Var ] -- Newly generated vars
                  )
freshTimeEnv timePreds = do
  freshVars <- replicateM (length timePreds) freshVar
  pure (M.fromList $ zip timePreds (TVar <$> freshVars), freshVars)


uniqTimePredsM :: HasTimePredicates a
               => MD.Metadata -> a -> Log.Logger [ PredicateSymbol ]
uniqTimePredsM metadata phi = nub . sort <$> timePreds metadata phi

class HasTimePredicates a where
  timePreds :: MD.Metadata -> a -> Log.Logger [ PredicateSymbol ]

instance HasTimePredicates Sentence where
  timePreds metadata sent =
    case sent of
      AG.SClause AG.Clause{..} -> (<>)
                              <$> timePreds metadata _head
                              <*> timePreds metadata _body
      AG.SQuery  AG.Query{..}  -> timePreds metadata _body
      AG.SFact   AG.Fact{..}   -> timePreds metadata _head

instance HasTimePredicates (Subgoal HOp Term) where
  timePreds metadata rho =
    case rho of
      AG.SAtom{..}              -> timePreds metadata _atom
      SHeadJump _ phi predSym _ -> (predSym :)
                               <$> timePreds metadata phi

instance HasTimePredicates (Subgoal (BOp 'Temporal) Term) where
  timePreds metadata rho =
    case rho of
      AG.SAtom{..}               -> timePreds metadata _atom
      SBodyJump _ phi timePred _ -> (timePred :) <$> timePreds metadata phi
      SBind _ timePred _ phi     -> (timePred :) <$> timePreds metadata phi
      SEX _ timePred phi         -> (timePred :) <$> timePreds metadata phi
      SAX _ timePred phi         -> (timePred :) <$> timePreds metadata phi
      SEF _ timePred phi         -> (timePred :) <$> timePreds metadata phi
      SAF _ timePred phi         -> (timePred :) <$> timePreds metadata phi
      SEG _ timePred phi         -> (timePred :) <$> timePreds metadata phi
      SAG _ timePred phi         -> (timePred :) <$> timePreds metadata phi
      SEU _ timePred phi psi     -> (\xs ys -> timePred : xs <> ys)
                                <$> timePreds metadata phi
                                <*> timePreds metadata psi
      SAU _ timePred phi psi     -> (\xs ys -> timePred : xs <> ys)
                                <$> timePreds metadata phi
                                <*> timePreds metadata psi
      AG.SNullOp{}               -> pure []
      AG.SUnOp{..}               -> timePreds metadata _child
      AG.SBinOp{..}              -> (<>)
                                <$> timePreds metadata _child1
                                <*> timePreds metadata _child2

instance HasTimePredicates (AtomicFormula Term) where
  timePreds metadata AtomicFormula{..} =
    MD.timingPreds <$> _predSym `MD.lookupM` metadata

type VarTypeEnv  = M.Map Var                TermType
type PredTypeEnv = M.Map PredicateSymbol [ TermType ]

type TypeEnv = (VarTypeEnv, PredTypeEnv)

type TypeEnvMT = StateT TypeEnv

runTypeEnvMT :: Monad m => TypeEnvMT m a -> m (a, PredTypeEnv)
runTypeEnvMT action = second snd <$> runStateT action (M.empty, M.empty)

addAtomType :: AG.AtomicFormula Term -> ClauseM ()
addAtomType AG.AtomicFormula{..} = do
  types <- (`traverse` _terms) $ \case
    TVar v  -> do
      mType <- lift $ getVarType v

      maybe
        (lift . lift . lift . lift $ Log.scream (Just _span) $
          "Type of " <> pp v <> " is unknown.") pure mType
    TSym s  -> pure $ AG.termType s
    TWild{} -> lift . lift . lift . lift $
      Log.scream (Just _span) "No wildcards in auxillary atoms."

  lift $ modify (second (M.insert _predSym types))

getVarTypeEnv :: Monad m => TypeEnvMT m VarTypeEnv
getVarTypeEnv = fst <$> get

getVarType :: Monad m => Var -> TypeEnvMT m (Maybe TermType)
getVarType var = M.lookup var <$> getVarTypeEnv

addVarType :: Var -> TermType -> ClauseM ()
addVarType var termType = do
  mType <- lift $ getVarType var
  case mType of
    Just termType'
      | termType == termType -> pure ()
      | otherwise -> lift . lift . lift . lift $ Log.scream Nothing $
        "Variable " <> pp var <> " cannot have two types: " <>
        pp termType <> " and " <> pp termType'
    Nothing -> lift $ modify (first (M.insert var termType))

addTimeVarType :: MD.Metadata -> Var -> PredicateSymbol -> ClauseM ()
addTimeVarType metadata var timePredSym = do
  predInfo <- lift . lift . lift . lift $ timePredSym `MD.lookupM` metadata
  case MD.typ predInfo of
    [ termType, _ ] -> addVarType var termType
    _               -> lift . lift . lift . lift $
      Log.scream (Just $ span var) "Time predicate does not has arity 2."

freshTypedTimeVar :: MD.Metadata -> PredicateSymbol -> ClauseM Var
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

type ClauseM = TimeEnvMT (TypeEnvMT (FreshVarMT (CompilerMT Log.Logger)))

runClauseM :: [ Var ]
           -> TimeEnv
           -> ClauseM a
           -> CompilerMT Log.Logger (a, PredTypeEnv)
runClauseM vars timeEnv action =
  runFreshVarMT vars (runTypeEnvMT (runTimeEnvMT action timeEnv))
