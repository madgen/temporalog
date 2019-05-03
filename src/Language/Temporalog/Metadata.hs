{-# LANGUAGE DataKinds #-}
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
  , lookupJoin
  , deleteJoin
  ) where

import Protolude hiding (diff, pred)

import           Data.List (partition)
import qualified Data.Map.Strict as M

import qualified Text.PrettyPrint as PP

import           Language.Exalog.Pretty.Helper
import qualified Language.Exalog.Logger as Log
import           Language.Exalog.SrcLoc (dummySpan)

import qualified Language.Vanillalog.Generic.AST as AG

import qualified Language.Temporalog.Util.Trie as T

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

type PredicateMetadata = M.Map PredicateSymbol PredicateInfo
type JoinMetadata      = T.Trie PredicateSymbol (Subgoal (BOp 'Explicit 'Temporal) Term)

type Metadata = (PredicateMetadata, JoinMetadata)

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

lookup :: PredicateSymbol -> Metadata -> Maybe PredicateInfo
lookup pSym = lookup' pSym . fst

lookup' :: PredicateSymbol -> PredicateMetadata -> Maybe PredicateInfo
lookup' = M.lookup

lookupM :: PredicateSymbol -> Metadata -> Log.Logger PredicateInfo
lookupM pSym = lookupM' pSym . fst

lookupM' :: PredicateSymbol -> PredicateMetadata -> Log.Logger PredicateInfo
lookupM' predSym predMetadata =
  case predSym `lookup'` predMetadata of
    Just predInfo -> pure predInfo
    Nothing -> Log.scream Nothing $ "No metadata for " <> pp predSym <> "."

lookupJoin :: [ PredicateSymbol ]
           -> Metadata
           -> Maybe ([ PredicateSymbol ], Subgoal (BOp 'Explicit 'Temporal) Term)
lookupJoin key (_,joinTrie) = key `T.lookup` joinTrie

deleteJoin :: [ PredicateSymbol ] -> Metadata -> Metadata
deleteJoin key = second (T.delete key)

-- |Enter new predicate metadata
addAuxillaryAtemporalPred :: PredicateSymbol
                          -> [ TermType ]
                          -> Metadata
                          -> Metadata
addAuxillaryAtemporalPred predSym predType = first $
  M.insert predSym $ PredicateInfo
    { _originalType = predType
    , _timings      = []
    , _auxillary    = True
    }

--------------------------------------------------------------------------------
-- Metadata processing
--------------------------------------------------------------------------------

processMetadata :: Program eleb -> Log.Logger Metadata
processMetadata pr = do
  predMetadata <- processPredDecl (predicateDeclarations pr)
  joinMetadata <- processJoinDecl predMetadata (joinDeclarations pr)
  pure (predMetadata, joinMetadata)

--------------------------------------------------------------------------------
-- Predicate declaration processing
--------------------------------------------------------------------------------

-- |Extract metadata from predicate declarations
processPredDecl :: [ PredicateDeclaration ] -> Log.Logger PredicateMetadata
processPredDecl predDecls = do
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

  processTemporal :: PredicateMetadata
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

--------------------------------------------------------------------------------
-- Join declaration processing
--------------------------------------------------------------------------------

processJoinDecl :: PredicateMetadata
                -> [ JoinDeclaration ]
                -> Log.Logger JoinMetadata
processJoinDecl predMetadata joinDecls = do
  checkJoins predMetadata joinDecls
  foldrM insertJoin T.empty joinDecls
  where
  insertJoin JoinDeclaration{..} trie = do
    tPreds <- timingPreds <$> _joint `lookupM'` predMetadata
    pure $ T.insert tPreds (jointAtom _joint) trie

  jointAtom :: PredicateSymbol -> Subgoal (BOp 'Explicit temp) Term
  jointAtom pSym = SAtom dummySpan $ AtomicFormula
    { _span    = dummySpan
    , _predSym = pSym
    , _terms   = []
    }

checkJoins :: PredicateMetadata -> [ JoinDeclaration ] -> Log.Logger ()
checkJoins metadata joinDecls = do
  traverse_ (checkJoinTemporality metadata) joinDecls

  checkJoinUniqueness metadata joinDecls

-- |Checks if join predicates are arity zero and temporal with respect to
-- at least two different predicates.
checkJoinTemporality :: PredicateMetadata -> JoinDeclaration -> Log.Logger ()
checkJoinTemporality metadata JoinDeclaration{..} = do
  predInfo <- _joint `lookupM'` metadata

  unless (arity predInfo - length (timingPreds predInfo) == 0) $
    Log.scold (Just _span) $
      "The join predicate " <> pp _joint <> " takes non-temporal parameters."

  case timingPreds predInfo of
    []             -> Log.scold (Just _span) $
      "The join predicate " <> pp _joint <> " has no time predicates."
      <> " It needs at least two."
    [ timingPred ] -> Log.scold (Just _span) $
      "The join predicate " <> pp _joint <> " has a single time predicate "
      <> pp timingPred <> ". It needs at least two."
    _              -> pure ()

checkJoinUniqueness :: PredicateMetadata -> [ JoinDeclaration ] -> Log.Logger ()
checkJoinUniqueness metadata joinDecls = void $ foldrM go [] joinDecls
  where
  go JoinDeclaration{..} acc = do
    predInfo <- _joint `lookupM'` metadata
    let timePredSyms = timingPreds predInfo

    let isOverlapping as bs = as `isPrefixOf` bs || bs `isPrefixOf` as

    when (any (timePredSyms `isOverlapping`) acc) $
      Log.scold (Just _span) $
        "Different joins cannot more general than one another."
        <> " Intersection of their time predicates should be smaller than both."

    pure $ timePredSyms : acc

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Metadata where
  pretty (predMetadata, joinMetadata) =
    pretty predMetadata PP.$+$ pretty joinMetadata

instance Pretty PredicateMetadata where
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
