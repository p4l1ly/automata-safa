{-# LANGUAGE LambdaCase #-}

module Afa.Lib.Free where

import Control.Monad.Free
import Data.Traversable
import Control.Lens
import Data.Functor.Classes

freeModChilds :: Functor m
  => LensLike m (f (Free f i)) (g (Free g j)) (Free f i) (Free g j)
  -> (i -> m j)
  -> Free f i
  -> m (Free g j)
freeModChilds setter lLeaf = rec where
  rec (Pure i) = Pure <$> lLeaf i
  rec (Free x) = Free <$> setter rec x

freeTraversal :: Applicative m
  => LensLike m (f (Free f i)) (g j) (Free f i) j
  -> LensLike m (Free f i) (Either i (g j)) (Free f i) j
freeTraversal setter rec = \case
  Pure i -> pure$ Left i
  Free t -> Right<$> setter rec t
