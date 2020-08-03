{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module Afa where

import Control.Arrow
import Control.Monad (join)
import Data.Array
import Data.Functor.Compose
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Pure (cocoScan)
import Data.Functor.Foldable.Dag.TreeHybrid (TreeHybrid(..))
import qualified Data.Functor.Foldable.Dag.Utils as Dag.Utils
import Data.Functor.Foldable.Dag.TreeHybrid.Utils
  ( treehybridizeTreeDag
  , Swallow(..)
  )
import qualified Data.Functor.Foldable.Dag.TreeHybrid.Utils as TreeDag.Utils
import Data.List
import Data.Maybe
import Data.Monoid

import Afa.Simplify (simplify_alg)
import Afa.Prism (isRecursive)
import Afa.TreeDag.Patterns.Builder


data Afa = Afa
  { varCount :: Int
  , terms :: Array Int Term
  , states :: Array Int Int
  }
  deriving (Show, Eq)


followRefs :: Afa -> Afa
followRefs afa@Afa{terms, states} = afa{states=fmap follow states} where
  follow ix = case terms!ix of Ref ix' -> follow ix'; _ -> ix


swallowOnlyChilds :: Afa -> Afa
swallowOnlyChilds afa@Afa{terms, states} = afa{terms = terms', states = states'}
  where
    (ixMapping, terms') = treehybridizeTreeDag swallow terms
    states' = fmap (ixMapping!) states

    extPtrMask = array (bounds terms)$
      fmap (, False) (indices terms) ++ map (, True) (elems states)

    swallow ix parentCount t
      | isRecursive (project t) =
          if parentCount > 1 || extPtrMask!ix then Keep else Swallow
      | otherwise = if extPtrMask!ix then Copy else Swallow


simplify :: Afa -> Afa
simplify afa@Afa{terms} = afa{terms=fmap (cata simplify_alg) terms}


cost :: Afa -> (Int, Int)
cost = TreeDag.Utils.cost . terms


costFixpoint :: (Afa -> Afa) -> Afa -> Afa
costFixpoint fn afa = fixpoint where
  iters = map (cost &&& id)$ iterate fn afa
  Just ((_, fixpoint), _) =
    find (\((c1, _), (c2, _)) -> c1 <= c2)$ zip iters (tail iters)


removeOrphans :: Afa -> Afa
removeOrphans afa@Afa{terms, states} =
  afa{terms = terms', states = fmap (ixMapping!) states}
  where
    (ixMapping, terms') = Dag.Utils.removeOrphans$ accum
      (\(a1, t) a2 -> (a1 || a2, t))
      (fmap (False,) terms)
      (map (, True)$ elems states)
