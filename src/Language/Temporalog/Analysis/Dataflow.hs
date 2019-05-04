{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Temporalog.Analysis.Dataflow
  (
  ) where

import Protolude

import qualified Data.Map.Strict as M
import qualified Data.Vector.Sized as V

import Language.Exalog.Core

data Label ann =
    LPred
      { _predicateBox :: PredicateBox ann
      , _paramIndex   :: Int
      , _polarity     :: Polarity
      }
  | LSym { _sym :: Sym }

deriving instance Identifiable (PredicateAnn ann) b => Eq (Label ann)

data SidewaySt ann = SidewaySt
  { _binderMap :: M.Map Var (Label ann)
  , _nodes     :: [ Label ann ]
  , _edges     :: [ (Label ann, Label ann) ]
  }

initSidewaySt = SidewaySt M.empty [] []

type Sideway ann = State (SidewaySt ann)

execSideway :: Sideway ann a -> ([ Label ann ], [ (Label ann, Label ann) ])
execSideway act | sidewaySt <- (`execState` initSidewaySt) act =
  (_nodes sidewaySt, _edges sidewaySt)

addSidewayNode :: Label ann -> Sideway ann ()
addSidewayNode node = modify (\st -> st {_nodes = node : _nodes st})

addSidewayEdge :: (Label ann, Label ann) -> Sideway ann ()
addSidewayEdge edge = modify (\st -> st {_edges = edge : _edges st})

getBinder :: Var -> Sideway ann (Maybe (Label ann))
getBinder var = M.lookup var . _binderMap <$> get

updateBinder :: Var -> Label ann -> Sideway ann ()
updateBinder var binder =
  modify (\st -> st {_binderMap = M.insert var binder $ _binderMap st})

addSidewayLiteral :: Literal ann -> Sideway ann ()
addSidewayLiteral Literal{..} = (`traverse_` zip [0..] (V.toList terms)) $ \case
  (ix, TVar var) -> do
    let dstLabel = LPred (PredicateBox predicate) ix polarity
    addSidewayNode dstLabel
    -- Maybe add an edge
    traverse_ (addSidewayEdge . (,dstLabel)) =<< getBinder var
    -- Update the binder to the current label
    updateBinder var dstLabel
  _              -> pure ()

sidewayInfo :: Clause ann -> ([ Label ann ], [ (Label ann, Label ann) ])
sidewayInfo Clause{..} = execSideway $ traverse_ addSidewayLiteral body
