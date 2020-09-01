{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

module Afa where

import Control.Arrow
import Control.Monad (join)
import Control.Monad.State
import Control.Monad.ST
import Data.Array
import Data.Array.ST (freeze)
import Data.Bitraversable
import Data.Foldable (toList)
import Data.Functor.Compose
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Consing (hashState_empty, hashCons, HashState(..))
import Data.Functor.Foldable.Dag.Monadic (cataScanM)
import Data.Functor.Foldable.Dag.Pure (cataScan)
import Data.Functor.Foldable.Dag.TreeHybrid (TreeHybrid(..), treeDagCataScanMAlg, treeDagAlg)
import qualified Data.Functor.Foldable.Dag.Utils as Dag.Utils
import Data.Functor.Foldable.Dag.TreeHybrid.Utils
  ( treehybridizeTreeDag
  , treehybridizeDag
  , Swallow(..)
  )
import qualified Data.Functor.Foldable.Dag.TreeHybrid.Utils as TreeDag.Utils
import Data.List
import Data.Maybe
import Data.Monoid

import Afa.Simplify (simplify_alg)
import Afa.Prism (isRecursive)
import Afa.TreeDag.Patterns.Builder
import qualified Afa.Functor as F


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


hashConsThenSwallow :: Afa -> Afa
hashConsThenSwallow afa@Afa{terms, states} = afa{terms = terms2, states = states2}
  where

  ixMapping1 :: Array Int Int
  (ixMapping1, HashState len termsList _) = runST$ flip runStateT hashState_empty$
    cataScanM (treeDagCataScanMAlg$ hashCons id . sortUniq) terms
    >>= lift . freeze

  sortUniq :: F.Term Int -> F.Term Int
  sortUniq (F.And ixs) = F.And$ map head$ group$ sort ixs
  sortUniq (F.Or ixs) = F.Or$ map head$ group$ sort ixs
  sortUniq x = x

  terms1 :: Array Int (F.Term Int)
  terms1 = listArray (0, len - 1)$ reverse termsList

  states1 = fmap (ixMapping1!) states

  extPtrMask = array (bounds terms1)$
    fmap (, False) (indices terms1) ++ map (, True) (elems states1)

  swallow ix parentCount t
    | isRecursive (project t) =
        if parentCount > 1 || extPtrMask!ix then Keep else Swallow
    | otherwise = if extPtrMask!ix then Copy else Swallow

  (ixMapping2, terms2) = treehybridizeDag swallow terms1
  states2 = fmap (ixMapping2!) states1


separateTerminals :: (Functor f, Foldable f) => f b -> Either (f b) (f a)
separateTerminals node
  | null (toList node) = Right (fmap undefined node)
  | otherwise = Left node


removeLiteralStates :: Term -> Afa -> Maybe Afa
removeLiteralStates lit afa@Afa{terms, states}
  | qixLit 0 = Nothing
  | otherwise = Just afa{terms = terms', states = states'}
  where
  qixLit ix = terms!(states!ix) == lit
  qixMap = listArray (0, length list - 1) list
    where list = scanl (\ix q -> if qixLit ix then ix else succ ix) 0$ elems states

  terms' = (`fmap` terms)$ cata$ \case
    Compose (Left ix)
      | qixLit ix -> lit
      | otherwise -> Ref$ qixMap!ix
    t -> embed t

  states' = array (0, length list - 1) list
    where list = filter (not . qixLit . fst)$ assocs states


-- | If Nothing is returned, the language of the Afa is universal.
-- | WARNING: this operation should not be applied before concatenation (and
-- | other operations where the length of the accepted word is relevant).
removeTrueStates :: Afa -> Maybe Afa
removeTrueStates = removeLiteralStates LTrue


-- | If Nothing is returned, the language of the Afa is empty.
-- | This operation should not affect anything negatively (contrary to
-- | removeTrueStates).
removeFalseStates :: Afa -> Maybe Afa
removeFalseStates = removeLiteralStates LFalse
