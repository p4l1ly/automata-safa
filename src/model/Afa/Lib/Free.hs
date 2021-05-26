{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}

module Afa.Lib.Free where

import Control.Monad.Free
import Data.Traversable
import Control.Lens
import Data.Functor.Classes

{-# INLINABLE freeModChilds #-}
freeModChilds :: Functor m
  => LensLike m (f (Free f i)) (g (Free g j)) (Free f i) (Free g j)
  -> LensLike m (Free f i) (Free g j) i j
freeModChilds !setter !lLeaf = rec where
  rec (Pure !i) = Pure <$> lLeaf i
  rec (Free !x) = Free <$> setter rec x

{-# INLINABLE freeAppMFun #-}
freeAppMFun
  :: ((Free f i -> Free g j) -> f (Free f i) -> g (Free g j))
  -> (i -> j) -> Free f i -> Free g j
freeAppMFun !setter !lLeaf = rec where
  rec (Pure !i) = Pure$ lLeaf i
  rec (Free !x) = Free$ setter rec x

{-# INLINABLE freeFor_ #-}
freeFor_ :: Functor m
  => LensLike m (f (Free f i)) () (Free f i) ()
  -> LensLike m (Free f i) () i ()
freeFor_ !setter !lLeaf = rec where
  rec (Pure !i) = lLeaf i
  rec (Free !x) = setter rec x

{-# INLINABLE freeTraversal #-}
freeTraversal :: Applicative m
  => LensLike m (f (Free f i)) x (Free f i) j
  -> LensLike m (Free f i) (Either i x) (Free f i) j
freeTraversal !setter !rec = \case
  Pure !i -> pure$ Left i
  Free !t -> Right<$> setter rec t
