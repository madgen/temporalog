{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Temporalog.Analysis.Dataflow
  (
  ) where

import Protolude hiding (sym)

import qualified Data.Map.Strict as M
import qualified Data.Vector.Sized as V

import Language.Exalog.Core

data EdgeLabel = Head | Vertical | Horizontal

data ProtoNode ann =
    NPred
      { _predicateBox :: PredicateBox ann
      , _paramIndex   :: Int
      , _polarity     :: Polarity
      }
  | NSym { _sym :: Sym }

deriving instance Identifiable (PredicateAnn ann) b => Eq (ProtoNode ann)

type ProtoEdge ann  = (ProtoNode ann, EdgeLabel, ProtoNode ann)
type ProtoGraph ann = ([ ProtoNode ann ], [ ProtoEdge ann ])

data HorizontalSt ann = HorizontalSt
  { _binderMap :: M.Map Var (ProtoNode ann)
  , _nodes     :: [ ProtoNode ann ]
  , _edges     :: [ ProtoEdge ann ]
  }

initHorizontalSt = HorizontalSt M.empty [] []

type Horizontal ann = State (HorizontalSt ann)

execHorizontal :: Horizontal ann a -> ProtoGraph ann
execHorizontal act | horizontalSt <- (`execState` initHorizontalSt) act =
  (_nodes horizontalSt, _edges horizontalSt)

addHorizontalNode :: ProtoNode ann -> Horizontal ann ()
addHorizontalNode node = modify (\st -> st {_nodes = node : _nodes st})

addHorizontalEdge :: ProtoEdge ann -> Horizontal ann ()
addHorizontalEdge edge = modify (\st -> st {_edges = edge : _edges st})

getBinder :: Var -> Horizontal ann (Maybe (ProtoNode ann))
getBinder var = M.lookup var . _binderMap <$> get

updateBinder :: Var -> ProtoNode ann -> Horizontal ann ()
updateBinder var binder =
  modify (\st -> st {_binderMap = M.insert var binder $ _binderMap st})

addHorizontalLiteral :: Literal ann -> Horizontal ann ()
addHorizontalLiteral Literal{..} = (`traverse_` zip [0..] (V.toList terms)) $ \case
  (ix, TVar var) -> do
    let dst = mkPredNode ix
    addHorizontalNode dst
    -- Maybe add an edge
    traverse_ (addHorizontalEdge . (, Horizontal, dst)) =<< getBinder var
    -- Update the binder to the current label
    updateBinder var dst
  (ix, TSym sym) -> do
    let src = NSym sym
    let dst = mkPredNode ix
    addHorizontalEdge (src, Horizontal, dst)
  _              -> pure ()
  where
  mkPredNode ix = NPred (PredicateBox predicate) ix polarity

horizontalInfo :: Clause ann -> ProtoGraph ann
horizontalInfo Clause{..} = execHorizontal $ traverse_ addHorizontalLiteral body
