{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}

module Language.Temporalog.Transformation.TimeParameter (extendWithTime) where

import Protolude

import Data.List (nub)
import Data.Text (pack)

import qualified Data.Map.Strict as M

import           Language.Vanillalog.Generic.Transformation.Util (transformM)
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (SrcSpan, Spannable(..))

import qualified Language.Temporalog.Metadata as MD
import           Language.Temporalog.AST

extendWithTime :: MD.Metadata
               -> AG.Program Void HOp (BOp AtOn)
               -> Log.LoggerM (AG.Program Void HOp (BOp AtOn))
extendWithTime metadata = transformM go
  where
  timingPredM AtomicFormula{..} =
    MD.timingPred <$> _predSym `MD.lookupM` metadata

  generateMap :: Sentence
              -> [ AG.AtomicFormula Term ]
              -> Log.LoggerM (M.Map PredicateSymbol Var)
  generateMap sent atoms = do
    timingPreds <- nub . catMaybes <$> traverse timingPredM atoms
    let varGenAction = traverse (\pred -> (pred,) <$> freshVar sent) timingPreds
    pure $ M.fromList $ evalState varGenAction 0

  collect :: Sentence -> Log.LoggerM (M.Map PredicateSymbol Var)
  collect s@AG.SFact{_fact = AG.Fact{..}}       = generateMap s (AG.atoms _head)
  collect s@AG.SClause{_clause = AG.Clause{..}} = generateMap s (AG.atoms _head <> AG.atoms _body)
  collect s@AG.SQuery{_query = AG.Query{..}}    =
    case _head of
      Nothing -> generateMap s (AG.atoms _body)
      Just _  -> Log.scream (Just _span)
        "Queries should not have been assigned heads."

  go :: Sentence -> Log.LoggerM Sentence
  go sent = do
    timingVarMap <- collect sent
    transformM (extendTerms timingVarMap) sent

  extendTerms :: M.Map PredicateSymbol Var
              -> AtomicFormula Term
              -> Log.LoggerM (AtomicFormula Term)
  extendTerms timingVarMap atom@AtomicFormula{..} = do
    mTimingPredSym <- timingPredM atom
    case mTimingPredSym of
      Nothing -> pure atom
      Just timingPredSym
        | Just var <- timingPredSym `M.lookup` timingVarMap ->
          pure AtomicFormula{_terms = _terms <> [ TVar var ],..}
        | otherwise -> Log.scream (Just _span)
          "Timing predicate is not mapped to a variable."

freshVar :: Sentence -> State Int Var
freshVar sentence = go
  where
  vs = vars sentence
  go = do
    i <- get
    modify (+ 1)
    let candidateVar = Var (span sentence) ("Time" <> (pack . show) i)
    if candidateVar `elem` vs
      then go
      else pure candidateVar
