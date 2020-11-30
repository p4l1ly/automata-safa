{-# LANGUAGE ViewPatterns #-}

module Afa.Lib where

import Data.Hashable.Lifted
import Data.List.NonEmpty (NonEmpty(..), toList)
import Data.Array

instance Hashable1 NonEmpty where
  liftHashWithSalt h salt (a :| as) = liftHashWithSalt h (h salt a) as

nonEmptyConcatMap :: (a -> NonEmpty b) -> NonEmpty a -> NonEmpty b
nonEmptyConcatMap f ((f -> h:|hs):|xs) = h :| hs ++ concatMap (toList . f) xs

listArray' :: [a] -> Array Int a
listArray' as = listArray (0, length as - 1) as

(>&>) :: Functor f => (a -> f b) -> (b -> c) -> a -> f c
ff >&> f = fmap f . ff
infixr 1 >&>
