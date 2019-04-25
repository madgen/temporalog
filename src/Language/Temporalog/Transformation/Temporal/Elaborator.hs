{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Temporalog.Transformation.Temporal.Elaborator
  ( elaborate
  ) where

import Protolude

import           Data.Functor.Foldable (Base, cataA)
import qualified Data.Set as S
import qualified Data.Text as T

import Language.Exalog.Pretty (pp)
import Language.Exalog.SrcLoc (SrcSpan)
import Language.Exalog.Logger

import qualified Language.Vanillalog.Generic.AST as AG

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

type Elaboration = ReaderT MD.Metadata Logger

elaborate :: MD.Metadata -> Program 'Implicit -> Logger (Program 'Explicit)
elaborate metadata AG.Program{..} = (`runReaderT` metadata) $ do
  newStatements <- traverse elaborateStatement _statements
  pure AG.Program{_statements = newStatements, ..}

elaborateStatement :: Statement 'Implicit -> Elaboration (Statement 'Explicit)
elaborateStatement AG.StDeclaration{..} = pure AG.StDeclaration{..}
elaborateStatement AG.StSentence{..}    =
  (\s -> AG.StSentence{_sentence = s, ..}) <$> elaborateSentence _sentence

elaborateSentence :: Sentence 'Implicit -> Elaboration (Sentence 'Explicit)
elaborateSentence (AG.SQuery AG.Query{..}) = do
  newHead <- sequence $ elaborateHead <$> _head
  newBody <- elaborateBody _body
  pure $ AG.SQuery AG.Query{_head = newHead, _body = newBody, ..}
elaborateSentence (AG.SFact AG.Fact{..}) = do
  newHead <- elaborateHead _head
  pure $ AG.SFact AG.Fact{_head = newHead, ..}
elaborateSentence (AG.SClause AG.Clause{..}) = do
  newHead <- elaborateHead _head
  newBody <- elaborateBody _body
  pure $ AG.SClause AG.Clause{_head = newHead, _body = newBody, ..}

determineTime :: TimeSym 'Implicit
              -> S.Set PredicateSymbol
              -> SrcSpan
              -> Elaboration (Maybe PredicateSymbol)
determineTime timeSym timePreds span =
  case timeSym of
    Exp timePred -> pure $ Just timePred
    Imp          ->
      case S.elems timePreds of
        []           -> pure Nothing
        [ timePred ] -> pure $ Just timePred
        timePreds'   -> lift $ scold (Just span) $
          "Temporal expression is ambiguous. Time predicate may be one of: "
          <> T.intercalate ", " (map pp timePreds')

elaborateHead :: Subgoal (HOp 'Implicit) a
              -> Elaboration (Subgoal (HOp 'Explicit) a)
elaborateHead = fmap fst <$> cataA alg
  where
  alg :: Base (Subgoal (HOp 'Implicit) a)
              (Elaboration (Subgoal (HOp 'Explicit) a, S.Set PredicateSymbol))
      -> Elaboration (Subgoal (HOp 'Explicit) a, S.Set PredicateSymbol)
  alg (SAtomF span atom)                    = elaborateAtom span atom
  alg (SHeadJumpF span action timeSym time) = do
    (phi, timePreds) <- action
    mTimePred <- determineTime timeSym timePreds span
    case mTimePred of
      Just timePred -> pure
        ( SHeadJump span phi (Exp timePred) time
        , timePred `S.delete` timePreds
        )
      Nothing      -> pure (phi, timePreds)

elaborateAtom :: SrcSpan
              -> AtomicFormula a
              -> Elaboration (Subgoal op a, S.Set PredicateSymbol)
elaborateAtom span atom@AG.AtomicFormula{..} = do
  metadata  <- ask
  timePreds <- lift $ MD.timingPreds <$> _predSym `MD.lookupM` metadata
  pure (SAtom span atom, S.fromList timePreds)

elaborateBody :: Subgoal (BOp 'Implicit temp) a
              -> Elaboration (Subgoal (BOp 'Explicit temp) a)
elaborateBody = fmap fst <$> cataA alg
  where
  alg :: Base (Subgoal (BOp 'Implicit temp) a)
              (Elaboration (Subgoal (BOp 'Explicit temp) a
                           , S.Set PredicateSymbol))
      -> Elaboration (Subgoal (BOp 'Explicit temp) a, S.Set PredicateSymbol)
  alg (AG.SAtomF span atom) = elaborateAtom span atom
  alg (SBodyJumpF span action timeSym time) = do
    (phi, timePreds) <- action
    mTimePred <- determineTime timeSym timePreds span
    case mTimePred of
      Just timePred -> pure
        ( SBodyJump span phi (Exp timePred) time
        , timePred `S.delete` timePreds
        )
      Nothing      -> pure (phi, timePreds)
  alg (SBindF span timeSym var action) = do
    (phi, timePreds) <- action
    mTimePred <- determineTime timeSym timePreds span
    case mTimePred of
      Just timePred -> pure
        ( SBind span (Exp timePred) var phi
        , timePred `S.insert` timePreds
        )
      Nothing      -> lift $
        scold (Just span) "Time predicate of the bind is ambiguous."
  alg AG.SNullOpF{..} = do
    mOp <- elaborateBodyOp _nullOpF S.empty _spanF
    case mOp of
      Just op -> pure (AG.SNullOp{_nullOp = op, _span = _spanF}, S.empty)
      Nothing -> lift $
        scream (Just _spanF) "Nullary operator couldn't be elaborated."
  alg AG.SUnOpF{_childF = act,..} = do
    (phi, timePreds) <- act
    mOp <- elaborateBodyOp _unOpF timePreds _spanF
    pure $ case mOp of
      Just op -> ( AG.SUnOp{_child = phi, _span = _spanF, _unOp = op}
                 , maybe timePreds (`S.insert` timePreds) (timePred op)
                 )
      Nothing -> (phi, timePreds)
  alg AG.SBinOpF{_child1F = act1, _child2F = act2, ..} = do
    (phi, timePreds1) <- act1
    (psi, timePreds2) <- act2
    let timePreds = timePreds1 `S.union` timePreds2
    mOp <- elaborateBodyOp _binOpF timePreds _spanF
    pure $ case mOp of
      Just op ->
        ( AG.SBinOp
            { _child1 = phi
            , _child2 = psi
            , _span   = _spanF
            , _binOp  = op}
        , maybe timePreds (`S.insert` timePreds) (timePred op)
        )
      Nothing -> (psi, timePreds)

elaborateBodyOp :: forall temp a
                 . BOp 'Implicit temp a
                -> S.Set PredicateSymbol
                -> SrcSpan
                -> Elaboration (Maybe (BOp 'Explicit temp a))
elaborateBodyOp op timePreds span = do
  e <- case op of
         Negation         -> pure $ Left Negation
         Conjunction      -> pure $ Left Conjunction
         Disjunction      -> pure $ Left Disjunction
         Dogru            -> pure $ Left Dogru
         AX timeSym       -> pure $ Right (AX, timeSym)
         EX timeSym       -> pure $ Right (EX, timeSym)
         AG timeSym       -> pure $ Right (AG, timeSym)
         EG timeSym       -> pure $ Right (EG, timeSym)
         AF timeSym       -> pure $ Right (AF, timeSym)
         EF timeSym       -> pure $ Right (EF, timeSym)
         AU timeSym       -> pure $ Right (AU, timeSym)
         EU timeSym       -> pure $ Right (EU, timeSym)
         _                -> lift $ scream Nothing
          "Hybrid operators shouldn't reach this far in elaboration."
    :: Elaboration
         (Either (BOp 'Explicit temp a)
                 ( TimeSym 'Explicit -> BOp 'Explicit temp a
                 , TimeSym 'Implicit
                 ))

  case e of
    Right (constructor, timeSym) -> do
      mPredSym <- determineTime timeSym timePreds span
      case mPredSym of
        Just predSym -> pure $ Just (constructor (Exp predSym))
        Nothing      -> pure Nothing
    Left constructor -> pure $ Just constructor
