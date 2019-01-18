{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.AtEliminator where

import Protolude

import Data.Functor.Foldable (Base, embed, cata)

import           Language.Vanillalog.Generic.Transformation.Util
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

eliminateAt :: MD.Metadata
            -> Program
            -> Log.LoggerM (AG.Program Declaration (Const Void) BOp)
eliminateAt metadata AG.Program{..} =
  (\sts -> AG.Program{_statements = sts,..}) <$> traverse eliminateAtSt _statements
  where
  eliminateAtSt :: Statement -> Log.LoggerM (AG.Statement Declaration (Const Void) BOp)
  eliminateAtSt AG.StSentence{..} =
    (\sent -> AG.StSentence{_sentence = sent,..}) <$> eliminateAtSent _sentence
  eliminateAtSt AG.StDeclaration{..} = pure AG.StDeclaration{..}

  eliminateAtSent :: Sentence -> Log.LoggerM (AG.Sentence (Const Void) BOp)
  eliminateAtSent AG.SClause{..} =
    (\clause -> AG.SClause{_clause = clause,..}) <$> eliminateAtClause _clause
  eliminateAtSent AG.SQuery{..} =
    (\q -> AG.SQuery{_query = q,..}) <$> eliminateAtQuery _query
  eliminateAtSent AG.SFact{..} =
    (\fact -> AG.SFact{_fact = fact,..}) <$> eliminateAtFact _fact

  eliminateAtClause :: Clause -> Log.LoggerM (AG.Clause (Const Void) BOp)
  eliminateAtClause AG.Clause{..} =
    (\head -> AG.Clause{_head = head,..}) <$> eliminateAtHeadSub _head

  eliminateAtQuery :: Query -> Log.LoggerM (AG.Query (Const Void) BOp)
  eliminateAtQuery AG.Query{_head = Just _head,..} =
    Log.scream (Just _span) "Query naming should not have happened."
  eliminateAtQuery AG.Query{_head = Nothing,..} =
    pure AG.Query{_head = Nothing,..}

  eliminateAtFact :: Fact -> Log.LoggerM (AG.Fact (Const Void))
  eliminateAtFact AG.Fact{..}=
    (\head -> AG.Fact{_head = head,..}) <$> eliminateAtHeadSub _head

  eliminateAtHeadSub :: Subgoal HOp Term -> Log.LoggerM (AG.Subgoal (Const Void) Term)
  eliminateAtHeadSub = cata alg
    where
    alg :: Algebra (Base (Subgoal HOp Term))
                   (Log.LoggerM (AG.Subgoal (Const Void) Term))
    alg (SAtomF span atom) = pure $ SAtom span atom
    alg (SHeadAtF span childM time) = do
      child <- childM
      case child of
        SAtom span atom -> SAtom span <$> (atom `overrideTime` time)
        _               -> Log.scold (Just span)
          "@ operator does not yet support for compund subgoals."

  overrideTime :: AtomicFormula Term -> Term -> Log.LoggerM (AtomicFormula Term)
  overrideTime atom@AtomicFormula{..} time = do
    info <- _predSym `MD.lookupM` metadata
    if MD.hasTiming info
      then
        case initMay _terms of
          Just initTerms -> pure AtomicFormula{_terms = initTerms <> [ time ],..}
          Nothing        -> Log.scream (Just _span)
            "Timed atom doesn't have a time parameter."
      else Log.whisper (Just _span) "No time parameter to affect." >> pure atom
