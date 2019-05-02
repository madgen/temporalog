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

import           Data.List ((\\), nub, partition)
import qualified Data.Map.Strict as M

import qualified Text.PrettyPrint as PP

import           Language.Exalog.Pretty.Helper
import qualified Language.Exalog.Logger as Log
import           Language.Exalog.SrcLoc (span, dummySpan)

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

  uniquenessCheck decls

  sentenceExistenceCheck sentences decls

  declarationExistenceCheck sentences decls

  let (temporalDecls, aTemporalDecls) = partition (isJust . _timePredSyms) decls

  timePreds <- fmap join . (`traverse` temporalDecls) $ \case
    DeclPred{..} ->
      maybe
      (Log.scream (Just _span)
                  "Time predicate doesn't exist in a temporal declaration.")
      pure
      _timePredSyms
    DeclJoin{..} -> _

  let (timingDecls, deductiveDecls) =
        partition ((`elem` timePreds) . #_predSym . _atomType) aTemporalDecls

  let timingMap    = M.fromList  $  map processATemporal                 timingDecls
  let deductiveMap = M.fromList  $  map processATemporal                 deductiveDecls
  temporalMap     <- M.fromList <$> traverse (processTemporal timingMap) temporalDecls

  pure $ timingMap `M.union` deductiveMap `M.union` temporalMap
  where
  processATemporal :: Declaration -> (PredicateSymbol, PredicateInfo)
  processATemporal DeclPred{..} =
    ( #_predSym _atomType
    , PredicateInfo
      { _originalType = _terms _atomType
      , _timings      = []
      , _auxillary    = False
      }
    )
  processATemporal DeclJoin{..} = _

  processTemporal :: Metadata
                  -> Declaration
                  -> Log.Logger (PredicateSymbol, PredicateInfo)
  processTemporal metadata DeclPred{..} = do
    tSyms <- maybe (Log.scream Nothing "Processing an atemporal predicate.") pure
      _timePredSyms

    predInfos <- maybe (Log.scream Nothing "Existence check is flawed.") pure $
      sequence $ (`M.lookup` metadata) <$> tSyms

    typs <- maybe
      (Log.scream Nothing "Timing sanity checking is flawed. Zero arity." )
      pure $
      sequence $ head . _originalType <$> predInfos

    pure ( #_predSym _atomType
         , PredicateInfo
           { _originalType = _terms _atomType
           , _timings      = uncurry Timing <$>
             -- Time predicates always appear in the same order.
             sortBy (\a b -> fst a `compare` fst b) (zip tSyms typs)
           , _auxillary    = False
           }
         )
  processTemporal metadata DeclJoin{..} = _

-- |Make sure there no repeated declarations for the same predicate.
uniquenessCheck :: [ Declaration ] -> Log.Logger ()
uniquenessCheck decls = do
  let predSyms = map (#_predSym . _atomType) decls
  let diff = predSyms \\ nub predSyms :: [ PredicateSymbol ]
  case head diff of
    Nothing              -> pure ()
    Just repeatedPred -> do
      let repeatedDecls = (`filter` decls) $ \case
            DeclPred{..} -> #_predSym _atomType == repeatedPred
            DeclJoin{..} -> _
      case head . map span $ repeatedDecls  of
        Just s  -> Log.scold (Just s) $
          "The declaration for predicate " <> pp repeatedPred <> " is repeated."
        Nothing -> Log.scream Nothing $
          "Could not find a declaration for " <> pp repeatedPred <> "."

-- |Check all predicates appearing in declarations have corresponding clauses
-- defining them.
sentenceExistenceCheck :: [ Sentence eleb ] -> [ Declaration ] -> Log.Logger ()
sentenceExistenceCheck sentences decls = forM_ decls $ \case
  DeclPred{..} -> do
    let declaredPredSym = #_predSym _atomType
    checkExistence _span declaredPredSym

    maybe (pure ()) (mapM_ (checkExistence _span)) _timePredSyms
  DeclJoin{..} -> _
  where
  checkExistence span pred =
    unless (pred `elem` predsBeingDefined) $
      Log.scold (Just span) $ "Predicate " <> pp pred <> " lacks a definition."

  predsBeingDefined = (`mapMaybe` sentences) $ \case
    AG.SQuery{}                                  -> Nothing
    AG.SFact{_fact     = AG.Fact{_head   = sub}} -> Just $ name sub
    AG.SClause{_clause = AG.Clause{_head = sub}} -> Just $ name sub

name :: Subgoal (HOp eleb) term -> PredicateSymbol
name AG.SAtom{..}          = #_predSym _atom
name (SHeadJump _ sub _ _) = name sub

-- |Check all predicates defined have corresponding declarations.
declarationExistenceCheck :: [ Sentence eleb ]
                          -> [ Declaration ]
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
