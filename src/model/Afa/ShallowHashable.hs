module Afa.ShallowHashable where

import Data.Hashable

class ShallowEq x where
  shallowEq :: x -> x -> Bool

class ShallowEq x => ShallowHashable x where
  shallowHash :: Int -> x -> Int


hashWithSalt' :: Int -> Int -> Int
hashWithSalt' = hashWithSalt
