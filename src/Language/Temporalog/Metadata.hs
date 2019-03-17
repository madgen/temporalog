{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Temporalog.Metadata
  ( Metadata
  , PredicateInfo
  , processMetadata
  , lookup
  , lookupM
  , typ
  , arity
  , timingPreds
  , hasTiming
  ) where

import Protolude

import           Data.List ((\\), nub, partition)
import qualified Data.Map.Strict as M

import qualified Text.PrettyPrint as PP

import           Language.Exalog.Pretty.Helper

import           Language.Vanillalog.Generic.Pretty
import qualified Language.Vanillalog.Generic.AST as AG
import qualified Language.Vanillalog.Generic.Logger as Log
import           Language.Vanillalog.Generic.Parser.SrcLoc (span, dummySpan)

import Language.Temporalog.AST

data Timing = Timing
  { _predSym :: AG.PredicateSymbol
  , _type    :: TermType
  }

data PredicateInfo = PredicateInfo
  { _originalType   :: [ TermType ]
  , _timings        :: [ Timing ] -- Ordered by predicate symbol
  }

typ :: PredicateInfo -> [ TermType ]
typ PredicateInfo{..} = _originalType <> map _type _timings

arity :: PredicateInfo -> Int
arity = length . typ

hasTiming :: PredicateInfo -> Bool
hasTiming PredicateInfo{..} = not . null $ _timings

timingPreds :: PredicateInfo -> [ AG.PredicateSymbol ]
timingPreds PredicateInfo{..} = (\Timing{..} -> _predSym) <$> _timings

type Metadata = M.Map AG.PredicateSymbol PredicateInfo

lookup :: AG.PredicateSymbol -> Metadata -> Maybe PredicateInfo
lookup = M.lookup

lookupM :: AG.PredicateSymbol -> Metadata -> Log.LoggerM PredicateInfo
lookupM predSym metadata =
  case predSym `lookup` metadata of
    Just predInfo -> pure predInfo
    Nothing -> Log.scream Nothing $ "No metadata for " <> pp predSym <> "."

-- |Extract metadata from declarations
processMetadata :: Program -> Log.LoggerM Metadata
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

  timePreds <- fmap join . (`traverse` temporalDecls) $ \Declaration{..} -> maybe
    (Log.scream (Just _span)
                "Time predicate doesn't exist in a temporal declaration.")
    pure
    _timePredSyms

  let (timingDecls, deductiveDecls) =
        partition ((`elem` timePreds) . #_predSym . _atomType) aTemporalDecls

  let timingMap    = M.fromList  $  map processATemporal                 timingDecls
  let deductiveMap = M.fromList  $  map processATemporal                 deductiveDecls
  temporalMap     <- M.fromList <$> traverse (processTemporal timingMap) temporalDecls

  pure $ timingMap `M.union` deductiveMap `M.union` temporalMap
  where
  processATemporal :: Declaration -> (AG.PredicateSymbol, PredicateInfo)
  processATemporal Declaration{..} =
    ( #_predSym _atomType
    , PredicateInfo
      { _originalType = _terms _atomType
      , _timings      = []
      }
    )

  processTemporal :: Metadata
                  -> Declaration
                  -> Log.LoggerM (AG.PredicateSymbol, PredicateInfo)
  processTemporal metadata Declaration{..} = do
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
           , _timings      = uncurry Timing
                         -- Make sure time predicates always appear in the
                         -- same order.
                         <$> sortBy (\a b -> fst a `compare` fst b)
                                    (zip tSyms typs)
           }
         )

-- |Make sure there no repeated declarations for the same predicate.
uniquenessCheck :: [ Declaration ] -> Log.LoggerM ()
uniquenessCheck decls = do
  let predSyms = map (#_predSym . _atomType) decls
  let diff = predSyms \\ nub predSyms :: [ PredicateSymbol ]
  case head diff of
    Nothing              -> pure ()
    Just repeatedPred -> do
      let repeatedDecls =
            filter ((repeatedPred ==) . #_predSym . _atomType) decls
      case head . map span $ repeatedDecls  of
        Just s  -> Log.scold (Just s) $
          "The declaration for predicate " <> pp repeatedPred <> " is repeated."
        Nothing -> Log.scream Nothing $
          "Could not find a declaration for " <> pp repeatedPred <> "."

-- |Check all predicates appearing in declarations have corresponding clauses
-- defining them.
sentenceExistenceCheck :: [ Sentence ] -> [ Declaration ] -> Log.LoggerM ()
sentenceExistenceCheck sentences decls = forM_ decls $ \Declaration{..} -> do
  let declaredPredSym = #_predSym _atomType
  checkExistence _span declaredPredSym

  maybe (pure ()) (mapM_ (checkExistence _span)) _timePredSyms
  where
  checkExistence span pred =
    unless (pred `elem` predsBeingDefined) $
      Log.scold (Just span) $ "Predicate " <> pp pred <> " lacks a definition."

  predsBeingDefined = (`mapMaybe` sentences) $ \case
    AG.SQuery{}                                  -> Nothing
    AG.SFact{_fact     = AG.Fact{_head   = sub}} -> Just $ name sub
    AG.SClause{_clause = AG.Clause{_head = sub}} -> Just $ name sub

name :: Subgoal HOp term -> AG.PredicateSymbol
name AG.SAtom{..}        = #_predSym _atom
name (SHeadAt _ sub _ _) = name sub

-- |Check all predicates defined have corresponding declarations.
declarationExistenceCheck :: [ Sentence ] -> [ Declaration ] -> Log.LoggerM ()
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

instance Pretty (AG.PredicateSymbol, PredicateInfo) where
  pretty (predSym, PredicateInfo{..}) =
    pretty AtomicFormula{ _span = dummySpan
                        , _predSym = predSym
                        , _terms = _originalType } PP.<+>
    (PP.vcat . prettyC) _timings

instance Pretty Timing where
  pretty Timing{..} =
    "@" PP.<+> pretty _predSym PP.<+> "with" PP.<+> pretty _type
