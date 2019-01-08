{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.TypeChecker (typeCheck) where

import Protolude

import Data.List (lookup)
import Data.Text (pack)

import           Language.Vanillalog.Generic.Transformation.Util (transformM)
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Pretty (pp)
import           Language.Vanillalog.Generic.Parser.SrcLoc (span)

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

type LocalTypeEnvironment  = [ (Var, TermType) ]

typeCheck :: MD.Metadata -> Program -> Log.LoggerM ()
typeCheck metadata program = void $ transformM (\s -> go s $> s) program
  where
  go :: Sentence -> Log.LoggerM ()
  go (AG.SFact   _ Fact{})        = pure ()
  go (AG.SQuery  _ AG.Query{..})  = check $ maybe [] (pure . fmap TVar) _head ++ AG.atoms _body
  go (AG.SClause _ AG.Clause{..}) = check $ _head                              : AG.atoms _body

  check :: [ AtomicFormula Term ] -> Log.LoggerM ()
  check = void . foldrM yakk []

  yakk :: AtomicFormula Term
       -> LocalTypeEnvironment
       -> Log.LoggerM LocalTypeEnvironment
  yakk atom@AtomicFormula{_fxSym = predSym, _span = s} localEnv =
    case predSym `MD.lookup` metadata of
      Just predInfo -> do
        arityCheck atom predInfo

        localEnvExtension <- unify (_terms atom) (MD.typ predInfo)
        foldrM add localEnv localEnvExtension
      Nothing -> Log.scream (Just s) $
        "There are no typing declarations for " <> predSym <> "."

arityCheck :: AtomicFormula Term -> MD.PredicateInfo -> Log.LoggerM ()
arityCheck AtomicFormula{..} predInfo = do
  let realArity = length _terms
  let expectedArity = MD.arity predInfo
  unless (realArity == expectedArity) $
    Log.scold (Just _span) $
      "Expected arity of " <> _fxSym <> " is " <> (pack . show) expectedArity <>
      " but its use has arity " <> (pack . show) realArity <> "."

add :: (Var, TermType)
    -> LocalTypeEnvironment
    -> Log.LoggerM LocalTypeEnvironment
add (var, tt) env =
  case var `lookup` env of
    Nothing -> pure $ (var, tt) : env
    Just tt'
      | tt == tt' -> pure env
      | otherwise -> Log.scold (Just $ span var) $
        pp var <> " was given the type " <> pp tt <>
        " but now is assigned " <> pp tt' <> "."

unify :: [ Term ] -> [ TermType ] -> Log.LoggerM LocalTypeEnvironment
unify terms types = catMaybes <$> traverse go (zip terms types)
  where
  go (AG.TVar var@AG.Var{}, tt) = pure $ Just (var, tt)
  go (AG.TSym sym, tt)
    | tt' <- AG.termType sym =
      if tt == tt'
        then pure Nothing
        else Log.scold (Just . span $ sym) $
          "Expected a " <> pp tt <> " but got a " <> pp tt' <> "."