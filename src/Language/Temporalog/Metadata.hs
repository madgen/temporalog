{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Temporalog.Metadata
  ( Metadata
  , PredicateInfo
  , processMetadata
  , lookup
  , typ
  , arity
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
  { _predSym :: Text
  , _type    :: TermType
  }

data PredicateInfo = PredicateInfo
  { _originalType   :: [ TermType ]
  , _timing         :: Maybe Timing
  }

typ :: PredicateInfo -> [ TermType ]
typ = _originalType

arity :: PredicateInfo -> Int
arity = length . typ

type Metadata = M.Map Text PredicateInfo

lookup :: Text -> Metadata -> Maybe PredicateInfo
lookup = M.lookup

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

  let (temporalDecls, aTemporalDecls) = partition (isJust . _timePredSym) decls

  timePreds <- (`traverse` temporalDecls) $ \Declaration{..} -> maybe
    (Log.scream (Just _span)
                "Time predicate doesn't exist in a temporal declaration.")
    pure
    _timePredSym

  let (timingDecls, deductiveDecls) =
        partition ((`elem` timePreds) . #_predSym . _atomType) aTemporalDecls

  let timingMap    = M.fromList  $  map processATemporal                 timingDecls
  let deductiveMap = M.fromList  $  map processATemporal                 deductiveDecls
  temporalMap     <- M.fromList <$> traverse (processTemporal timingMap) temporalDecls

  pure $ timingMap `M.union` deductiveMap `M.union` temporalMap
  where
  processATemporal :: Declaration -> (Text, PredicateInfo)
  processATemporal Declaration{..} =
    ( #_predSym _atomType
    , PredicateInfo
      { _originalType = _terms _atomType
      , _timing       = Nothing
      }
    )

  processTemporal :: Metadata
                  -> Declaration
                  -> Log.LoggerM (Text, PredicateInfo)
  processTemporal timingMap Declaration{..} = do
    tSym <- maybe (Log.scream Nothing "Processing an atemporal predicate.") pure
      _timePredSym

    metadata <- maybe (Log.scream Nothing "Existence check is flawed.") pure $
      tSym `M.lookup` timingMap

    typ <- maybe
      (Log.scream Nothing "Timing sanity checking is flawed. Zero arity." )
      pure
      (head . _originalType $ metadata)

    pure ( #_predSym _atomType
         , PredicateInfo
           { _originalType = _terms _atomType
           , _timing       = Just $ Timing { _predSym = tSym, _type = typ }
           }
         )

-- |Make sure there no repeated declarations for the same predicate.
uniquenessCheck :: [ Declaration ] -> Log.LoggerM ()
uniquenessCheck decls = do
  let predSyms = map (#_predSym . _atomType) decls
  let diff = predSyms \\ nub predSyms
  case head diff of
    Nothing              -> pure ()
    Just repeatedPredSym ->
      case head . map span . filter ((repeatedPredSym ==) . #_predSym . _atomType) $ decls of
        Just s  -> Log.scold (Just s) $
          "The declaration for predicate " <> repeatedPredSym <> " is repeated."
        Nothing -> Log.scream Nothing $
          "Could not find a declaration for " <> repeatedPredSym <> "."

-- |Check all predicates appearing in declarations have corresponding clauses
-- defining them.
sentenceExistenceCheck :: [ Sentence ] -> [ Declaration ] -> Log.LoggerM ()
sentenceExistenceCheck sentences decls = forM_ decls $ \Declaration{..} -> do
  let declaredPredSym = #_predSym _atomType
  checkExistence _span declaredPredSym

  maybe (pure ()) (checkExistence _span) _timePredSym
  where
  checkExistence span pred =
    unless (pred `elem` predsBeingDefined) $
      Log.scold (Just span) $ "Predicate " <> pred <> " lacks a definition."

  predsBeingDefined = (`mapMaybe` sentences) $ \case
    AG.SQuery{} -> Nothing
    AG.SFact{_fact     = AG.Fact{_atom   = AG.AtomicFormula{_predSym = sym}}} -> Just sym
    AG.SClause{_clause = AG.Clause{_head = AG.AtomicFormula{_predSym = sym}}} -> Just sym

-- |Check all predicates defined have corresponding declarations.
declarationExistenceCheck :: [ Sentence ] -> [ Declaration ] -> Log.LoggerM ()
declarationExistenceCheck sentences decls = forM_ sentences $ \case
  AG.SQuery{} -> pure ()
  AG.SFact{AG._fact     = AG.Fact{_atom   = AtomicFormula{_predSym = predSym}},..} ->
    checkExistence _span predSym
  AG.SClause{AG._clause = AG.Clause{_head = AtomicFormula{_predSym = predSym}},..} ->
    checkExistence _span predSym
  where
  checkExistence span pred =
    unless (pred `elem` predsBeingDeclared) $
      Log.scold (Just span) $ "Predicate " <> pred <> " lacks a declaration."

  predsBeingDeclared = map (#_predSym . _atomType) decls

instance Pretty Metadata where
  pretty = PP.vcat . prettyC . M.toList

instance Pretty (Text, PredicateInfo) where
  pretty (predSym, PredicateInfo{..}) =
    pretty AtomicFormula{ _span = dummySpan
                        , _predSym = predSym
                        , _terms = _originalType } PP.<+>
    case _timing of
      Just Timing{..} ->
        "@" PP.<+> pretty _predSym PP.<+> "with" PP.<+> pretty _type
      Nothing -> PP.empty
