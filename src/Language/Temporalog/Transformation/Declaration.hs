{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Temporalog.Transformation.Declaration
  ( removeDecls
  , checkDecls
  , checkJoins
  ) where

import Protolude hiding (pred, diff)

import Data.List (deleteFirstsBy, nubBy)

import qualified Language.Vanillalog.Generic.AST as AG

import Language.Exalog.Logger
import Language.Exalog.Pretty.Helper

import           Language.Temporalog.AST
import qualified Language.Temporalog.Metadata as MD

removeDecls :: forall eleb
             . Program eleb -> AG.Program Void (HOp eleb) (BOp eleb 'Temporal)
removeDecls AG.Program{..} = AG.Program{_statements = newStatements,..}
  where
  newStatements :: [ AG.Statement Void (HOp eleb) (BOp eleb 'Temporal) ]
  newStatements = map (\AG.StSentence{..} -> AG.StSentence{..})
                . filter (\case {AG.StSentence{} -> True; _ -> False})
                $ _statements

checkDecls :: [ Sentence eleb ] -> [ Declaration ] -> Logger ()
checkDecls sentences decls = do
  sentenceExistenceCheck sentences decls

  let (predDecls, joinDecls) = partitionEithers $ (<$> decls) $ \case
        DeclPred{..} -> Left _predDecl
        DeclJoin{..} -> Right _joinDecl

  predDeclUniquenessCheck predDecls
  joinDeclUniquenessCheck joinDecls

  declExistenceCheck sentences predDecls

-- |Make sure there no repeated declarations for the same predicate.
predDeclUniquenessCheck :: [ PredicateDeclaration ] -> Logger ()
predDeclUniquenessCheck predDecls = do
  let pSym = #_predSym . _atomType :: PredicateDeclaration -> PredicateSymbol
  let pSymEq a b = pSym a == pSym b
  let diff = deleteFirstsBy pSymEq predDecls (nubBy pSymEq predDecls)
  case head diff of
    Nothing                             -> pure ()
    Just pDecl@PredicateDeclaration{..} -> scold (Just _span) $
      "The declaration for predicate " <> pp (pSym pDecl)
      <> " is repeated."

-- |Warn if therea re repeated declarations of the same join.
joinDeclUniquenessCheck :: [ JoinDeclaration ] -> Logger ()
joinDeclUniquenessCheck joinDecls = do
  let joinEq a b = _joint a == _joint b
  let joinDiff = deleteFirstsBy joinEq joinDecls (nubBy joinEq joinDecls)
  case head joinDiff of
    Nothing                  -> pure ()
    Just JoinDeclaration{..} -> whisper (Just _span) $
        "The declaration for predicate " <> pp _joint <> " is repeated."

-- |Check all predicates appearing in declarations have corresponding clauses
-- defining them.
sentenceExistenceCheck :: [ Sentence eleb ] -> [ Declaration ] -> Logger ()
sentenceExistenceCheck sentences decls = forM_ decls $ \case
  DeclPred PredicateDeclaration{..} -> do
    let declaredPredSym = #_predSym _atomType
    checkExistence _span declaredPredSym

    maybe (pure ()) (traverse_ (checkExistence _span)) _timePredSyms
  DeclJoin JoinDeclaration{..} -> checkExistence _span _joint
  where
  checkExistence s pred =
    unless (pred `elem` predsBeingDefined) $
      scold (Just s) $ "Predicate " <> pp pred <> " lacks a definition."

  predsBeingDefined = (`mapMaybe` sentences) $ \case
    AG.SQuery{}                                  -> Nothing
    AG.SFact{_fact     = AG.Fact{_head   = sub}} -> Just $ name sub
    AG.SClause{_clause = AG.Clause{_head = sub}} -> Just $ name sub

-- |Check all predicates defined have corresponding declarations.
declExistenceCheck :: [ Sentence eleb ] -> [ PredicateDeclaration ] -> Logger ()
declExistenceCheck sentences decls = forM_ sentences $ \case
  AG.SQuery{} -> pure ()
  AG.SFact{AG._fact     = AG.Fact{_head   = sub,..}} ->
    checkExistence _span (name sub)
  AG.SClause{AG._clause = AG.Clause{_head = sub,..}} ->
    checkExistence _span (name sub)
  where
  checkExistence span pred =
    unless (pred `elem` predsBeingDeclared) $
      scold (Just span) $ "Predicate " <> pp pred <> " lacks a declaration."

  predsBeingDeclared = map (#_predSym . _atomType) decls

name :: Subgoal (HOp eleb) term -> PredicateSymbol
name AG.SAtom{..}          = #_predSym _atom
name (SHeadJump _ sub _ _) = name sub

checkJoins :: MD.Metadata -> [ JoinDeclaration ] -> Logger ()
checkJoins metadata joinDecls = do
  traverse_ (checkJoinTemporality metadata) joinDecls

  checkJoinUniqueness metadata joinDecls

-- |Checks if join predicates are arity zero and temporal with respect to
-- at least two different predicates.
checkJoinTemporality :: MD.Metadata -> JoinDeclaration -> Logger ()
checkJoinTemporality metadata JoinDeclaration{..} = do
  predInfo <- _joint `MD.lookupM` metadata

  unless (MD.arity predInfo - length (MD.timingPreds predInfo) == 0) $
    scold (Just _span) $
      "The join predicate " <> pp _joint <> " takes non-temporal parameters."

  case MD.timingPreds predInfo of
    []             -> scold (Just _span) $
      "The join predicate " <> pp _joint <> " has no time predicates."
      <> " It needs at least two."
    [ timingPred ] -> scold (Just _span) $
      "The join predicate " <> pp _joint <> " has a single time predicate "
      <> pp timingPred <> ". It needs at least two."
    _              -> pure ()

checkJoinUniqueness :: MD.Metadata -> [ JoinDeclaration ] -> Logger ()
checkJoinUniqueness metadata joinDecls = void $ foldrM go [] joinDecls
  where
  go JoinDeclaration{..} acc = do
    predInfo <- _joint `MD.lookupM` metadata
    let timePredSyms = MD.timingPreds predInfo

    let isOverlapping as bs = as `isPrefixOf` bs || bs `isPrefixOf` as

    when (any (timePredSyms `isOverlapping`) acc) $
      scold (Just _span) $
        "Different joins cannot more general than one another."
        <> " Intersection of their time predicates should be smaller than both."

    pure $ timePredSyms : acc
