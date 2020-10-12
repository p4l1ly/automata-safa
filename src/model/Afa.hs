module Afa where

import Data.Array

import Afa.Term.TreeF (Term)

data Afa = Afa
  { terms :: Array Int Term
  , states :: Array Int Int
  }
  deriving (Show, Eq)
