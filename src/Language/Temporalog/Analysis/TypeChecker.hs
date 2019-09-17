{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Analysis.TypeChecker (typeCheck) where

import Protolude hiding (sym)

import Data.List (lookup)
import Data.Text (pack)

import qualified Language.Exalog.Logger as Log
import           Language.Exalog.SrcLoc (span)

import qualified Language.Vanillalog.AST as A
import           Language.Vanillalog.Generic.Transformation.Util (transformM)
import           Language.Vanillalog.Generic.AST
import           Language.Vanillalog.Generic.Pretty (pp)

import qualified Language.Temporalog.Analysis.Metadata as MD

type LocalTypeEnvironment  = [ (Var, TermType) ]

typeCheck :: MD.Metadata -> A.Program -> Log.Logger ()
typeCheck metadata program =
  void $ transformM (\s -> go (atoms (s :: A.Sentence)) $> s) program
  where
  go :: [ AtomicFormula Term ] -> Log.Logger ()
  go = void . foldrM yakk [] . reverse

  yakk :: AtomicFormula Term
       -> LocalTypeEnvironment
       -> Log.Logger LocalTypeEnvironment
  yakk atom@AtomicFormula{_predSym = predSym, _span = s} localEnv =
    case predSym `MD.lookup` metadata of
      Just predInfo -> do
        arityCheck atom predInfo

        localEnvExtension <- unify (_terms atom) (MD.typ predInfo)
        foldrM add localEnv localEnvExtension
      Nothing -> Log.scream (Just s) $
        "There are no typing declarations for " <> pp predSym <> "."

arityCheck :: AtomicFormula Term -> MD.PredicateInfo -> Log.Logger ()
arityCheck AtomicFormula{..} predInfo = do
  let realArity = length _terms
  let expectedArity = MD.arity predInfo
  unless (realArity == expectedArity) $
    Log.scold (Just _span) $
      "Expected arity of " <> pp _predSym <> " is " <> (pack . show) expectedArity <>
      " but its use has arity " <> (pack . show) realArity <> "."

add :: (Var, TermType)
    -> LocalTypeEnvironment
    -> Log.Logger LocalTypeEnvironment
add (var, tt) env =
  case var `lookup` env of
    Nothing -> pure $ (var, tt) : env
    Just tt'
      | tt == tt' -> pure env
      | otherwise -> Log.scold (Just $ span var) $
        pp var <> " was assigned type " <> pp tt <>
          " but it is used as " <> pp tt' <> "."

unify :: [ Term ] -> [ TermType ] -> Log.Logger LocalTypeEnvironment
unify terms types = catMaybes <$> traverse go (zip terms types)
  where
  go (TVar var@Var{}, tt) = pure $ Just (var, tt)
  go (TSym sym, tt)
    | tt' <- termType sym =
      if tt == tt'
        then pure Nothing
        else Log.scold (Just . span $ sym) $
          "Expected a " <> pp tt <> " but got a " <> pp tt' <> "."
  go (TWild{}, _) = pure Nothing
