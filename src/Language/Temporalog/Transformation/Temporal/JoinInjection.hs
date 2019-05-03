{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.Temporal.JoinInjection
  ( injectJoins
  ) where

import Protolude

import Data.List (nub)
import Data.Functor.Foldable (Base, project)
import Data.Functor.Foldable.Exotic (anaM)

import           Language.Exalog.Logger
import           Language.Exalog.SrcLoc (span)

import qualified Language.Vanillalog.Generic.AST as AG

import           Language.Temporalog.AST
import           Language.Temporalog.Transformation.Temporal.Compiler (timePreds)
import qualified Language.Temporalog.Metadata as MD

injectJoins :: MD.Metadata
            -> AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal)
            -> Logger (AG.Program Void (HOp 'Explicit) (BOp 'Explicit 'Temporal))
injectJoins metadata AG.Program{..} = do
  newStatements <- traverse goSt _statements
  pure AG.Program{_statements = newStatements, ..}
  where
  goSt (AG.StSentence sent)    = AG.StSentence <$> goSent sent
  goSt (AG.StDeclaration decl) = pure $ absurd decl

  goSent sent@AG.SFact{..}          = pure sent
  goSent (AG.SClause AG.Clause{..}) = do
    newBody <- goBody _body
    pure $ AG.SClause AG.Clause{_body = newBody, ..}
  goSent (AG.SQuery AG.Query{..})   = do
    newBody <- goBody _body
    pure $ AG.SQuery AG.Query{_body = newBody, ..}

  goBody = anaM joinCoalg >=> injectJoin Nothing metadata

  joinCoalg :: Subgoal (BOp 'Explicit 'Temporal) Term
            -> Logger (Base (Subgoal (BOp 'Explicit 'Temporal) Term)
                            (Subgoal (BOp 'Explicit 'Temporal) Term))
  joinCoalg (SBodyJump sp phi tSym@(Exp tPred) time) = do
    rho <- injectJoin (Just tPred) metadata phi
    pure $ SBodyJumpF sp rho tSym time
  joinCoalg s = pure $ project s

injectJoin :: Maybe PredicateSymbol
           -> MD.Metadata
           -> Subgoal (BOp 'Explicit 'Temporal) Term
           -> Logger (Subgoal (BOp 'Explicit 'Temporal) Term)
injectJoin mDeletedTimePred metadata phi =
  (nub . sort <$> timePreds metadata phi) >>= go metadata
  where
  go meta tPreds =
    case tPreds `MD.lookupJoin` meta of
      Just (word, joint) -> do
        psi <- go (word `MD.deleteJoin` meta) tPreds
        case mDeletedTimePred of
          Just deletedTimePred | deletedTimePred `notElem` word -> pure psi
          _ -> pure $ SConj (span phi) joint psi
      Nothing -> pure phi
