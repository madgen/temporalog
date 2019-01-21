{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module Language.Temporalog.Transformation.Temporal.Hybrid (eliminateAt) where

import Protolude

import Data.Functor.Foldable (Base, embed, cata)

import           Language.Vanillalog.Generic.Transformation.Util
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

eliminateAt :: MD.Metadata
            -> AG.Program Void HOp (BOp AtOn)
            -> Log.LoggerM (AG.Program Void (Const Void) (BOp AtOff))
eliminateAt metadata AG.Program{..} =
  (\sts -> AG.Program{_statements = sts,..}) <$> traverse eliminateAtSt _statements
  where
  eliminateAtSt :: AG.Statement Void HOp (BOp AtOn)
                -> Log.LoggerM (AG.Statement Void (Const Void) (BOp AtOff))
  eliminateAtSt AG.StSentence{..} =
    (\sent -> AG.StSentence{_sentence = sent,..}) <$> eliminateAtSent _sentence
  eliminateAtSt AG.StDeclaration{..} = absurd _declaration

  eliminateAtSent :: Sentence -> Log.LoggerM (AG.Sentence (Const Void) (BOp AtOff))
  eliminateAtSent AG.SClause{..} =
    (\clause -> AG.SClause{_clause = clause,..}) <$> eliminateAtClause _clause
  eliminateAtSent AG.SQuery{..} =
    (\q -> AG.SQuery{_query = q,..}) <$> eliminateAtQuery _query
  eliminateAtSent AG.SFact{..} =
    (\fact -> AG.SFact{_fact = fact,..}) <$> eliminateAtFact _fact

  eliminateAtClause :: Clause -> Log.LoggerM (AG.Clause (Const Void) (BOp AtOff))
  eliminateAtClause AG.Clause{..} =
        (\head body -> AG.Clause{_head = head, _body = body,..})
    <$> eliminateAtHead _head
    <*> eliminateAtBody _body

  eliminateAtQuery :: Query -> Log.LoggerM (AG.Query (Const Void) (BOp AtOff))
  eliminateAtQuery AG.Query{_head = Just _head,..} =
    Log.scream (Just _span) "Query naming should not have happened."
  eliminateAtQuery AG.Query{_head = Nothing,..} =
    (\body -> AG.Query{_head = Nothing, _body = body,..}) <$> eliminateAtBody _body

  eliminateAtFact :: Fact -> Log.LoggerM (AG.Fact (Const Void))
  eliminateAtFact AG.Fact{..}=
    (\head -> AG.Fact{_head = head,..}) <$> eliminateAtHead _head

  eliminateAtHead :: Subgoal HOp Term
                  -> Log.LoggerM (AG.Subgoal (Const Void) Term)
  eliminateAtHead = cata alg
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

  eliminateAtBody :: Subgoal (BOp AtOn) Term
                  -> Log.LoggerM (AG.Subgoal (BOp AtOff) Term)
  eliminateAtBody = cata alg
    where
    alg :: Algebra (Base (Subgoal (BOp AtOn) Term))
                   (Log.LoggerM (AG.Subgoal (BOp AtOff) Term))
    alg (SAtomF span atom) = pure $ SAtom span atom
    alg (SBodyAtF span childM time) = do
      child <- childM
      case child of
        SAtom span atom -> SAtom span <$> (atom `overrideTime` time)
        _               -> Log.scold (Just span)
          "@ operator does not yet support for compund subgoals."
    alg (AG.SNullOpF span op)      = AG.SNullOp span <$> switchOff op
    alg (AG.SUnOpF span op c)      = AG.SUnOp   span <$> switchOff op <*> c
    alg (AG.SBinOpF span op c1 c2) = AG.SBinOp  span <$> switchOff op <*> c1 <*> c2

    switchOff :: BOp AtOn a -> Log.LoggerM (BOp AtOff a)
    switchOff Negation     = pure Negation
    switchOff Conjunction  = pure Conjunction
    switchOff Disjunction  = pure Disjunction
    switchOff Dogru        = pure Dogru
    switchOff AX           = pure AX
    switchOff EX           = pure EX
    switchOff AG           = pure AG
    switchOff EG           = pure EG
    switchOff AF           = pure AF
    switchOff EF           = pure EF
    switchOff AU           = pure AU
    switchOff EU           = pure EU
    switchOff (BodyAt term) =
      Log.scream Nothing "Unexpected @ encountered during elimination."

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
