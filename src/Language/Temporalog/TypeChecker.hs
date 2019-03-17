{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.TypeChecker (typeCheck) where

import Protolude

import Data.List (lookup)
import Data.Text (pack)

import qualified Language.Vanillalog.AST as A
import           Language.Vanillalog.Generic.Transformation.Util (transformM)
import           Language.Vanillalog.Generic.AST
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Pretty (pp)
import           Language.Vanillalog.Generic.Parser.SrcLoc (span)

import qualified Language.Temporalog.Metadata as MD

type LocalTypeEnvironment  = [ (Var, TermType) ]

typeCheck :: MD.Metadata -> A.Program -> Log.LoggerM ()
typeCheck metadata program = void
                          $ transformM (\s -> check (collect s) $> s) program
  where
  collect :: A.Sentence -> [ AtomicFormula Term ]
  collect (SFact   Fact{..})   = atoms _head
  collect (SQuery  Query{..})  = (fmap TVar <$> maybe [] atoms _head) ++ atoms _body
  collect (SClause Clause{..}) = atoms _head                          ++ atoms _body

  check :: [ AtomicFormula Term ] -> Log.LoggerM ()
  check = void . foldrM yakk [] . reverse

  yakk :: AtomicFormula Term
       -> LocalTypeEnvironment
       -> Log.LoggerM LocalTypeEnvironment
  yakk atom@AtomicFormula{_predSym = predSym, _span = s} localEnv =
    case predSym `MD.lookup` metadata of
      Just predInfo -> do
        arityCheck atom predInfo

        localEnvExtension <- unify (_terms atom) (MD.typ predInfo)
        foldrM add localEnv localEnvExtension
      Nothing -> Log.scream (Just s) $
        "There are no typing declarations for " <> pp predSym <> "."

arityCheck :: AtomicFormula Term -> MD.PredicateInfo -> Log.LoggerM ()
arityCheck AtomicFormula{..} predInfo = do
  let realArity = length _terms
  let expectedArity = MD.arity predInfo
  unless (realArity == expectedArity) $
    Log.scold (Just _span) $
      "Expected arity of " <> pp _predSym <> " is " <> (pack . show) expectedArity <>
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
        pp var <> " was assigned type " <> pp tt <>
          " but it is used as " <> pp tt' <> "."

unify :: [ Term ] -> [ TermType ] -> Log.LoggerM LocalTypeEnvironment
unify terms types = catMaybes <$> traverse go (zip terms types)
  where
  go (TVar var@Var{}, tt) = pure $ Just (var, tt)
  go (TSym sym, tt)
    | tt' <- termType sym =
      if tt == tt'
        then pure Nothing
        else Log.scold (Just . span $ sym) $
          "Expected a " <> pp tt <> " but got a " <> pp tt' <> "."
