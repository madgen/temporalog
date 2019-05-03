module Language.Temporalog.Util.Trie
  ( Trie
  , empty
  , insert
  , delete
  , flatten
  , lookup
  ) where

import Protolude hiding (empty)

import qualified Text.PrettyPrint as PP

import Language.Exalog.Pretty.Helper (Pretty(..))

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

-- |Trie lookup that ignores symbols when stuck. Returns the sequence used
-- to match as well as the value stored there.
lookup :: Eq a => [ a ] -> Trie a b -> Maybe ([ a ], b)
lookup as (Trie tNodes) = lookup' as tNodes

lookup' :: Eq a => [ a ] -> [ TNode a b ] -> Maybe ([ a ], b)
lookup' [] tNodes = do
  TLeaf b <- find (\case {TLeaf{} -> True; _ -> False}) tNodes
  pure ([], b)
lookup' (a : as) tNodes =
  case find (isMatchingNode a) tNodes of
    Just (TNode _ tNodes') -> first (a :) <$> lookup' as tNodes'
    _                      -> lookup' as tNodes

-- |Delete an exact sequence from the trie
delete :: Eq a => [ a ] -> Trie a b -> Trie a b
delete as (Trie tNodes) = Trie $ delete' as tNodes

delete' :: Eq a => [ a ] -> [ TNode a b ] -> [ TNode a b ]
delete' []       tNodes = filter (\case {TNode{} -> True; _ -> False}) tNodes
delete' (a : as) tNodes = (`mapMaybe` delete' as tNodes) $ \case
  TNode a' [] | a == a' -> Nothing
  t                     -> Just t

isMatchingNode :: Eq a => a -> TNode a b -> Bool
isMatchingNode _ TLeaf{}      = False
isMatchingNode a (TNode a' _) = a == a'

flatten :: Trie a b -> [ ([ a ], b) ]
flatten (Trie tNodes) = flatten' tNodes

flatten' :: [ TNode a b ] -> [ ([ a ], b) ]
flatten' tNodes = join $ (`map` tNodes) $ \case
  TLeaf b         -> [ ([], b) ]
  TNode a tNodes' -> first (a :) <$> flatten' tNodes'

instance (Pretty a, Pretty b) => Pretty (Trie a b) where
  pretty trie = PP.vcat $
    (\(as,b) -> prettyKey as PP.<+> "==>" PP.<+> pretty b) <$> flatten trie
    where
    prettyKey :: Pretty a => [ a ] -> PP.Doc
    prettyKey = PP.hcat . PP.punctuate ", " . map pretty
