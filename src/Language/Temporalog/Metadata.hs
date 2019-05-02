{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Temporalog.Metadata
  ( Metadata
  , PredicateInfo
  , processMetadata
  , addAuxillaryAtemporalPred
  , lookup
  , lookupM
  , typ
  , arity
  , isAuxillary
  , timingPreds
  , hasTiming
  ) where

import Protolude hiding (diff, pred)

import           Data.List (deleteFirstsBy, nubBy, partition)
import qualified Data.Map.Strict as M

import qualified Text.PrettyPrint as PP

import           Language.Exalog.Pretty.Helper
import qualified Language.Exalog.Logger as Log
import           Language.Exalog.SrcLoc (dummySpan)

import qualified Language.Vanillalog.Generic.AST as AG

import Language.Temporalog.AST

data Timing = Timing
  { _predSym :: PredicateSymbol
  , _type    :: TermType
  }

data PredicateInfo = PredicateInfo
  { _originalType :: [ TermType ]
  , _timings      :: [ Timing ] -- Ordered by predicate symbol
  , _auxillary    :: Bool
  }

typ :: PredicateInfo -> [ TermType ]
typ PredicateInfo{..} = _originalType <> map _type _timings

arity :: PredicateInfo -> Int
arity = length . typ

isAuxillary :: PredicateInfo -> Bool
isAuxillary = _auxillary

hasTiming :: PredicateInfo -> Bool
hasTiming PredicateInfo{..} = not . null $ _timings

timingPreds :: PredicateInfo -> [ PredicateSymbol ]
timingPreds PredicateInfo{..} = (\Timing{..} -> _predSym) <$> _timings

type Metadata = M.Map PredicateSymbol PredicateInfo

lookup :: PredicateSymbol -> Metadata -> Maybe PredicateInfo
lookup = M.lookup

lookupM :: PredicateSymbol -> Metadata -> Log.Logger PredicateInfo
lookupM predSym metadata =
  case predSym `lookup` metadata of
    Just predInfo -> pure predInfo
    Nothing -> Log.scream Nothing $ "No metadata for " <> pp predSym <> "."

-- |Enter new predicate metadata
addAuxillaryAtemporalPred :: PredicateSymbol -> [ TermType ] -> Metadata -> Metadata
addAuxillaryAtemporalPred predSym predType =
  M.insert predSym $ PredicateInfo
    { _originalType = predType
    , _timings      = []
    , _auxillary    = True
    }

-- |Extract metadata from declarations
processMetadata :: Program eleb -> Log.Logger Metadata
processMetadata program = do
  let (decls, sentences) =
          bimap (AG._declaration <$>) (AG._sentence <$>)
        . partition (\case {AG.StDeclaration{..} -> True; _ -> False})
        . AG._statements
        $ program

  sentenceExistenceCheck sentences decls

  let (predDecls, joinDecls) = partitionEithers $ (<$> decls) $ \case
        DeclPred{..} -> Left _predDecl
        DeclJoin{..} -> Right _joinDecl

  predDeclUniquenessCheck predDecls
  joinDeclUniquenessCheck joinDecls

  declarationExistenceCheck sentences predDecls

  let (temporalDecls, aTemporalDecls) =
        partition (isJust . _timePredSyms) predDecls

  timePreds <- fmap join . (`traverse` temporalDecls) $ \case
    PredicateDeclaration{..} ->
      maybe
      (Log.scream (Just _span)
                  "Time predicate doesn't exist in a temporal declaration.")
      pure
      _timePredSyms

  let (timingDecls, deductiveDecls) =
        partition ((`elem` timePreds) . #_predSym . _atomType) aTemporalDecls

  let timingMap    = M.fromList  $  map processATemporal                 timingDecls
  let deductiveMap = M.fromList  $  map processATemporal                 deductiveDecls
  temporalMap     <- M.fromList <$> traverse (processTemporal timingMap) temporalDecls

  let metadata = timingMap `M.union` deductiveMap `M.union` temporalMap

  traverse_ (checkJoinTemporality metadata) joinDecls

  checkJoinUniqueness metadata joinDecls

  pure metadata
  where
  processATemporal :: PredicateDeclaration -> (PredicateSymbol, PredicateInfo)
  processATemporal PredicateDeclaration{..} =
    ( #_predSym _atomType
    , PredicateInfo
      { _originalType = _terms _atomType
      , _timings      = []
      , _auxillary    = False
      }
    )

  processTemporal :: Metadata
                  -> PredicateDeclaration
                  -> Log.Logger (PredicateSymbol, PredicateInfo)
  processTemporal metadata PredicateDeclaration{..} = do
    tSyms <- maybe
      (Log.scream (Just _span) "Processing an atemporal predicate.")
      pure
      _timePredSyms

    predInfos <- maybe (Log.scream Nothing "Existence check is flawed.") pure $
      sequence $ (`M.lookup` metadata) <$> tSyms

    typs <- maybe
      (Log.scream (Just _span) "Timing sanity checking is flawed. Zero arity." )
      pure
      (sequence $ head . _originalType <$> predInfos)

    pure ( #_predSym _atomType
         , PredicateInfo
           { _originalType = _terms _atomType
           , _timings      = uncurry Timing <$>
             -- Time predicates always appear in the same order.
             sortBy (\a b -> fst a `compare` fst b) (zip tSyms typs)
           , _auxillary    = False
           }
         )

-- |Make sure there no repeated declarations for the same predicate.
predDeclUniquenessCheck :: [ PredicateDeclaration ] -> Log.Logger ()
predDeclUniquenessCheck predDecls = do
  let pSym = #_predSym . _atomType :: PredicateDeclaration -> PredicateSymbol
  let pSymEq a b = pSym a == pSym b
  let diff = deleteFirstsBy pSymEq predDecls (nubBy pSymEq predDecls)
  case head diff of
    Nothing                             -> pure ()
    Just pDecl@PredicateDeclaration{..} -> Log.scold (Just _span) $
      "The declaration for predicate " <> pp (pSym pDecl)
      <> " is repeated."

-- |Make sure there no repeated declarations for the same predicate.
joinDeclUniquenessCheck :: [ JoinDeclaration ] -> Log.Logger ()
joinDeclUniquenessCheck joinDecls = do
  let joinEq a b = _joint a == _joint b
  let joinDiff = deleteFirstsBy joinEq joinDecls (nubBy joinEq joinDecls)
  case head joinDiff of
    Nothing                  -> pure ()
    Just JoinDeclaration{..} -> Log.whisper (Just _span) $
        "The declaration for predicate " <> pp _joint <> " is repeated."

-- |Check all predicates appearing in declarations have corresponding clauses
-- defining them.
sentenceExistenceCheck :: [ Sentence eleb ] -> [ Declaration ] -> Log.Logger ()
sentenceExistenceCheck sentences decls = forM_ decls $ \case
  DeclPred PredicateDeclaration{..} -> do
    let declaredPredSym = #_predSym _atomType
    checkExistence _span declaredPredSym

    maybe (pure ()) (traverse_ (checkExistence _span)) _timePredSyms
  DeclJoin JoinDeclaration{..} -> checkExistence _span _joint
  where
  checkExistence s pred =
    unless (pred `elem` predsBeingDefined) $
      Log.scold (Just s) $ "Predicate " <> pp pred <> " lacks a definition."

  predsBeingDefined = (`mapMaybe` sentences) $ \case
    AG.SQuery{}                                  -> Nothing
    AG.SFact{_fact     = AG.Fact{_head   = sub}} -> Just $ name sub
    AG.SClause{_clause = AG.Clause{_head = sub}} -> Just $ name sub

name :: Subgoal (HOp eleb) term -> PredicateSymbol
name AG.SAtom{..}          = #_predSym _atom
name (SHeadJump _ sub _ _) = name sub

-- |Check all predicates defined have corresponding declarations.
declarationExistenceCheck :: [ Sentence eleb ]
                          -> [ PredicateDeclaration ]
                          -> Log.Logger ()
declarationExistenceCheck sentences decls = forM_ sentences $ \case
  AG.SQuery{} -> pure ()
  AG.SFact{AG._fact     = AG.Fact{_head   = sub,..}} ->
    checkExistence _span (name sub)
  AG.SClause{AG._clause = AG.Clause{_head = sub,..}} ->
    checkExistence _span (name sub)
  where
  checkExistence span pred =
    unless (pred `elem` predsBeingDeclared) $
      Log.scold (Just span) $ "Predicate " <> pp pred <> " lacks a declaration."

  predsBeingDeclared = map (#_predSym . _atomType) decls

-- |Checks if join predicates are arity zero and temporal with respect to
-- at least two different predicates.
checkJoinTemporality :: Metadata -> JoinDeclaration -> Log.Logger ()
checkJoinTemporality metadata JoinDeclaration{..} = do
  predInfo <- _joint `lookupM` metadata

  unless (null $ _originalType predInfo) $
    Log.scold (Just _span) $
      "The join predicate " <> pp _joint <> " takes non-temporal parameters."

  case _timings predInfo of
    []             -> Log.scold (Just _span) $
      "The join predicate " <> pp _joint <> " has no time predicates."
      <> " It needs at least two."
    [ Timing{..} ] -> Log.scold (Just _span) $
      "The join predicate " <> pp _joint <> " has a single time predicate "
      <> pp _predSym <> ". It needs at least two."
    _              -> pure ()

checkJoinUniqueness :: Metadata -> [ JoinDeclaration ] -> Log.Logger ()
checkJoinUniqueness metadata joinDecls = _

instance Pretty Metadata where
  pretty = PP.vcat . prettyC . M.toList

instance Pretty (PredicateSymbol, PredicateInfo) where
  pretty (predSym, PredicateInfo{..}) =
    pretty AtomicFormula{ _span = dummySpan
                        , _predSym = predSym
                        , _terms = _originalType } PP.<+>
    (PP.vcat . prettyC) _timings

instance Pretty Timing where
  pretty Timing{..} =
    "@" PP.<+> pretty _predSym PP.<+> "with" PP.<+> pretty _type
