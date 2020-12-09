module Afa.Convert.Separated.Model where

import Data.Void
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import Data.Array

data Afa p = Afa
  { aterms :: Array Int (BTerm.Term p Int)
  , qterms :: Array Int (MTerm.Term Void Int Int)
  , states :: Array Int [(Maybe Int, Maybe Int)]
  , initState :: Int
  }
