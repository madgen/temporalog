{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Temporalog.Transformation.GuardInjection
  ( injectGuards
  ) where

import Protolude hiding (head)

import           Data.List ((\\))
import qualified Data.List.NonEmpty as NE
import qualified Data.Graph.Inductive as Gr

import           Language.Exalog.Adornment (adornProgram)
import           Language.Exalog.Core
import           Language.Exalog.Dependency
import           Language.Exalog.Logger
import           Language.Exalog.WellModing (isWellModed, checkWellModability)

import qualified Language.Temporalog.Metadata as MD

injectGuards :: MD.Metadata -> Program 'ABase -> Logger (Program 'ABase)
injectGuards metadata pr@Program{..} = do
  injectedClausess <- traverse assessAndTransform temporalClusters

  pure $ Program
    { clauses = aTemporalClauses <> mconcat injectedClausess
    , ..}
  where
  temporalClusters :: [ Program 'ABase ]
  temporalClusters  = map isolateWithAuxillaries topLevelTemporalClauses

  aTemporalClauses :: [ Clause 'ABase ]
  aTemporalClauses =
    clauses \\ mconcat (map (\Program{clauses = clss} -> clss) temporalClusters)

  assessAndTransform :: Program 'ABase -> Logger [ Clause 'ABase ]
  assessAndTransform cluster@Program{clauses = clss}
    | isWellModed cluster = pure clss
    | otherwise = do
      checkWellModability (adornProgram cluster)
      injectGuard cluster

  injectGuard :: Program 'ABase -> Logger [ Clause 'ABase ]
  injectGuard Program{clauses = topClause : auxClauses} = _
  injectGuard Program{clauses = []} =
    scream Nothing "Empty cluster during guard injection."

  topLevelTemporalClauses :: [ Clause 'ABase ]
  topLevelTemporalClauses = filter isTopLevelTemporal clauses

  -- |A clause is top-level temporal clause if its
  -- + head is not an auxillary predicate
  -- + body contains an auxillary predicate
  isTopLevelTemporal :: Clause 'ABase -> Bool
  isTopLevelTemporal Clause{head = head, body = body} =
    not headIsAuxillary && bodyHasAuxillary
    where
    headIsAuxillary  = pBoxIsAuxillary . predicateBox $ head
    bodyHasAuxillary = or $ pBoxIsAuxillary . predicateBox <$> body

  pBoxIsAuxillary :: PredicateBox 'ABase -> Bool
  pBoxIsAuxillary (PredicateBox Predicate{fxSym = predSym}) =
    maybe False MD.isAuxillary (predSym `MD.lookup` metadata)

  depGr :: DependencyGr 'ABase
  depGr = dependencyGr . decorate $ pr

  -- |Find auxillary predicates that appear in the body of the clause and
  -- find the auxillary predicates that appear in the defining clauses of
  -- those auxillary predicates and so on.
  findDirectAuxillaries :: Clause 'ABase -> [ PredicateBox 'ABase ]
  findDirectAuxillaries Clause{body = body} =
    Gr.xdfsWith chooseNode Gr.lab' initialNodes depGr
    where
    -- |All the auxillary nodes that appear in clause body
    initialNodes :: [ Gr.Node ]
    initialNodes = (`mapMaybe` Gr.labNodes depGr) $ \(node, pBox) ->
      if pBox `elem` bodyAuxillaries then Just node else Nothing

    bodyAuxillaries :: [ PredicateBox 'ABase ]
    bodyAuxillaries = filter pBoxIsAuxillary $ NE.toList (predicateBox <$> body)

    -- |Exploit the fact that auxillary predicates are never acyclic except
    -- perhaps reflexive.
    chooseNode :: Gr.Context (PredicateBox 'ABase) b -> [ Gr.Node ]
    chooseNode (_, _, pBox, nextNodes) = (`mapMaybe` nextNodes) $
      \(_, node) -> do
        pBox' <- Gr.lab depGr node
        if pBox /= pBox' && pBoxIsAuxillary pBox'
          then Just node
          else Nothing

  -- |Create a little program that has the target clause and all auxillary
  -- clauses that descend from it. The query predicate is set to the target
  -- clause head predicate.
  isolateWithAuxillaries :: Clause 'ABase -> Program 'ABase
  isolateWithAuxillaries cl = Program
    { clauses    = cl : mconcat (search pr <$> findDirectAuxillaries cl)
    , queryPreds = [ predicateBox . head $ cl ]
    , annotation = annotation
    }
