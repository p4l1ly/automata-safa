{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Afa.ShallowHashable where

import Data.Hashable

newtype Shallow x = Shallow {unshallow :: x} deriving (Show, Functor, Foldable, Traversable)

shallowEq :: Eq (Shallow x) => x -> x -> Bool
shallowEq a b = Shallow a == Shallow b

shallowHash :: Hashable (Shallow x) => Int -> x -> Int
shallowHash salt = hashWithSalt salt . Shallow

hashWithSalt' :: Int -> Int -> Int
hashWithSalt' = hashWithSalt

type SameTraverse m t a = (a -> m a) -> t a -> m (t a)
