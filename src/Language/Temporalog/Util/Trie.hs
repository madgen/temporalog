module Language.Temporalog.Util.Trie
  ( Trie
  , empty
  , insert
  , lookup
  ) where

import Protolude hiding (empty)

newtype Trie a b = Trie [ TNode a b ]

data TNode a b =
    TNode a [ TNode a b ]
  | TLeaf b

empty :: Trie a b
empty = Trie [ ]

-- |Inserts a value at the end of a word. If there is a value at that
-- point, override.
insert :: Eq a => [ a ] -> b -> Trie a b -> Trie a b
insert as bs (Trie tNode) = Trie $ insert' as bs tNode

insert' :: Eq a => [ a ] -> b -> [ TNode a b ] -> [ TNode a b ]
insert' [] b tNodes = (`map` tNodes) $ \case
  TLeaf{} -> TLeaf b
  tNode   -> tNode
insert' (a : as) b tNodes =
  case find (isMatchingNode a) tNodes of
    Nothing -> TNode a (insert' as b []) : tNodes
    Just _  -> (`map` tNodes) $ \case
      TNode a' tNodes' | a == a' -> TNode a' (insert' as b tNodes')
      t -> t

lookup :: Eq a => [ a ] -> Trie a b -> Maybe b
lookup as (Trie tNodes) = lookup' as tNodes

lookup' :: Eq a => [ a ] -> [ TNode a b ] -> Maybe b
lookup' [] tNodes = do
  TLeaf b <- find (\case {TLeaf{} -> True; _ -> False}) tNodes
  pure b
lookup' (a : as) tNodes =
  case find (isMatchingNode a) tNodes of
    Just (TNode _ tNodes') -> lookup' as tNodes'
    _                      -> Nothing

isMatchingNode :: Eq a => a -> TNode a b -> Bool
isMatchingNode _ TLeaf{}      = False
isMatchingNode a (TNode a' _) = a == a'
