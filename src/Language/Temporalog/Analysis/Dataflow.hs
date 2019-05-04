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

data EdgeLabel = Vertical | Horizontal
data Use       = Head | Body Polarity deriving (Eq)

data Constant = CSym Sym | CWild deriving Eq

data ProtoNode ann =
    NPredicate
      { _predicateBox :: PredicateBox ann
      , _paramIndex   :: Int
      , _use          :: Use
      }
  | NConstant { _constant :: Constant }

deriving instance Identifiable (PredicateAnn ann) b => Eq (ProtoNode ann)

type ProtoEdge ann  = (ProtoNode ann, EdgeLabel, ProtoNode ann)
type ProtoGraph ann = ([ ProtoNode ann ], [ ProtoEdge ann ])

data SidewaysSt ann = SidewaysSt
  { _binderMap :: M.Map Var (ProtoNode ann)
  , _nodes     :: [ ProtoNode ann ]
  , _edges     :: [ ProtoEdge ann ]
  }

initSidewaysSt = SidewaysSt M.empty [] []

type Sideways ann = State (SidewaysSt ann)

execSideways :: Sideways ann a -> ProtoGraph ann
execSideways act | horizontalSt <- (`execState` initSidewaysSt) act =
  (_nodes horizontalSt, _edges horizontalSt)

addNode :: ProtoNode ann -> Sideways ann ()
addNode node = modify (\st -> st {_nodes = node : _nodes st})

addEdge :: ProtoEdge ann -> Sideways ann ()
addEdge edge = modify (\st -> st {_edges = edge : _edges st})

getBinder :: Var -> Sideways ann (Maybe (ProtoNode ann))
getBinder var = M.lookup var . _binderMap <$> get

updateBinder :: Var -> ProtoNode ann -> Sideways ann ()
updateBinder var binder =
  modify (\st -> st {_binderMap = M.insert var binder $ _binderMap st})

addBodyLiteral :: Literal ann -> Sideways ann ()
addBodyLiteral Literal{..} = do
  newNodes <- fmap join $ forM (zip [0..] (V.toList terms)) $ \case
    (ix, TVar var) -> do
      let dst = mkPredNode ix
      -- Maybe add an edge
      traverse_ (addEdge . (, Horizontal, dst)) =<< getBinder var
      -- Update the binder to the current label
      when (polarity == Positive) $ updateBinder var dst

      pure [ dst ]
    (ix, TSym sym) -> addConstant ix $ CSym sym
    (ix, TWild)    -> addConstant ix CWild

  forM_ newNodes addNode
  where
  addConstant ix constant = do
    let src = NConstant constant
    let dst = mkPredNode ix

    addEdge (src, Horizontal, dst)

    pure [ src, dst ]

  mkPredNode ix = NPredicate (PredicateBox predicate) ix (Body polarity)

sidewaysInfo :: Clause ann -> ProtoGraph ann
sidewaysInfo Clause{..} = execSideways $
  forM_ body addBodyLiteral
