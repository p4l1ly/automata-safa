module Ltl.Lib where

import Control.Monad
import Control.Monad.Free (Free(..))

bloom :: Functor f => (f (Free f a) -> Free f (Free f a)) -> Free f a -> Free f a
bloom b = rec where
  rec (Pure a) = Pure a
  rec (Free ff) = join$ b$ fmap rec ff

skippingAlg :: (a -> Free f a) -> a -> f (Free f a)
skippingAlg f = rec where rec a = case f a of Pure a -> rec a; Free f -> f
