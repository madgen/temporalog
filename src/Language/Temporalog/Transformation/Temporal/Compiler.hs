{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}

module Language.Temporalog.Transformation.Temporal.Compiler
  ( eliminateTemporal
  ) where

import Protolude


import Control.Arrow ((>>>))

import Data.Functor.Foldable (Base, cata, embed)
import Data.Text (pack)

import qualified Language.Vanillalog.AST as A
import           Language.Vanillalog.Generic.Transformation.Util (Algebra)
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span)

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
