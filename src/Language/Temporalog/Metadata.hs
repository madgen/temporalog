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

import           Data.List (partition)
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
processMetadata :: [ PredicateDeclaration ] -> Log.Logger Metadata
processMetadata predDecls = do
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

  pure $ timingMap `M.union` deductiveMap `M.union` temporalMap
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
