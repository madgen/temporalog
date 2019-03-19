{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}

module Language.Temporalog.Transformation.Temporal.Compiler
  ( eliminateTemporal
  ) where

import Protolude


import Control.Arrow ((>>>))

import           Data.Functor.Foldable (Base, cata, embed)
import           Data.Text (pack)
import qualified Data.Map.Strict as M

import           Language.Vanillalog.Generic.Transformation.Util (Algebra)
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span, dummySpan)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

type CompilerMT = StateT ( ([ AG.PredicateSymbol ], Int)
                         , [ AG.Clause (Const Void) (Const Void) ]
                         )

runCompilerMT :: Monad m
              => CompilerMT m a
              -> [ AG.PredicateSymbol ]
              -> m (a, [ AG.Clause (Const Void) (Const Void) ])
runCompilerMT action predSyms = second snd <$> runStateT action ((predSyms, 1), [ ])

addClause :: Monad m => AG.Clause (Const Void) (Const Void) -> CompilerMT m ()
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

freshTimeEnv :: MD.Metadata -> AG.Clause b c -> FreshVarMT Log.LoggerM TimeEnv
freshTimeEnv metadata cl@AG.Clause{..} = do
  timePredSyms <- lift timePredSymsM
  freshVars <- fmap TVar <$> replicateM (length timePredSyms) freshVar
  pure $ M.fromList $ zip timePredSyms freshVars
  where
  predSyms = map #_predSym $ AG.atoms _head <> AG.atoms _body
  timePredSymsM = concatMap MD.timingPreds
             <$> traverse (`MD.lookupM` metadata) predSyms

-- |Assembles a clause
mkClause :: PredicateSymbol              -- |Name of the predicate to define
         -> [ Term ]                     -- |Argument list
         -> AG.Subgoal (Const Void) Term -- |Body formula
         -> AG.Clause (Const Void) (Const Void)
mkClause headPredSym args body =
  AG.Clause (span body)
    (SAtom (span body)
      (AtomicFormula (span body) headPredSym args)) body

eliminateTemporal :: MD.Metadata
                  -> AG.Program Void HOp (BOp 'Temporal)
                  -> Log.LoggerM (AG.Program Void (Const Void) (BOp 'ATemporal))
eliminateTemporal metadata AG.Program{..} = _
  where

  goClause :: AG.Clause HOp (BOp 'Temporal)
           -> CompilerMT Identity (AG.Clause HOp (BOp 'Temporal))
  goClause = _

  goSub :: AG.Subgoal (BOp 'Temporal) Term
        -> CompilerMT Identity (AG.Subgoal (BOp 'Temporal) Term)
  goSub = _
