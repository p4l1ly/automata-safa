{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}

module Afa.Lib.Tree where

import Data.Traversable
import Control.Lens
import Data.Functor.Classes

newtype Tree f i = Tree (Either i (f (Tree f i)))
pattern Node x = Tree (Right x)
pattern Leaf i = Tree (Left i)

instance (Eq i, Eq1 f) => Eq (Tree f i) where
  Leaf a == Leaf b = a == b
  Node a == Node b = eq1 a b

instance (Show i, Show1 f) => Show (Tree f i) where
  showsPrec d (Leaf a) = showParen (d >= 11)$ showString "Leaf " . showsPrec 11 a 
  showsPrec d (Node a) = showParen (d >= 11)$ showString "Node " . showsPrec1 11 a 

treeModChilds :: Functor m
  => LensLike m (f (Tree f i)) (g (Tree g j)) (Tree f i) (Tree g j)
  -> (i -> m j)
  -> Tree f i
  -> m (Tree g j)
treeModChilds setter lLeaf = rec where
  rec (Leaf i) = Leaf <$> lLeaf i
  rec (Node x) = Node <$> setter rec x

instance Traversable f => Functor (Tree f) where fmap = fmapDefault
instance Traversable f => Foldable (Tree f) where foldMap = foldMapDefault
instance Traversable f => Traversable (Tree f) where traverse = treeModChilds traverse

treeTraversal :: Applicative m
  => LensLike m (f (Tree f i)) (g j) (Tree f i) j
  -> (Tree f i -> m j) -> Tree f i -> m (Either i (g j))
treeTraversal setter rec = \case
  Leaf i -> pure$ Left i
  Node t -> Right<$> setter rec t
