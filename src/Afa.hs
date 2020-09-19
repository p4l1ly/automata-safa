{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Afa where

import Control.Arrow
import Control.Monad (join)
import Control.Monad.State
import Control.Monad.ST
import Data.Array
import Data.Array.Unsafe (unsafeFreeze)
import Data.Bitraversable
import Data.Foldable (toList)
import Data.Functor.Compose
import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Consing (hashCons', runHashConsMonadT)
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
import qualified Afa.TreeDag
import qualified Afa.Functor as F
import qualified Afa.StatePositiveness
import qualified Afa.Prism


data Afa = Afa
  { terms :: Array Int Term
  , states :: Array Int Int
  }
  deriving (Show, Eq)


followRefs :: Afa -> Afa
followRefs afa@Afa{terms, states} = afa{states=fmap follow states} where
  follow ix = case terms!ix of Ref ix' -> follow ix'; _ -> ix

getExtPtrMask terms ptrs = array (bounds terms)$
  fmap (, False) (indices terms) ++ map (, True) ptrs

swallowOnlyChilds :: Afa -> Afa
swallowOnlyChilds afa@Afa{terms, states} = afa{terms = terms', states = states'}
  where
    (ixMapping, terms') = treehybridizeTreeDag swallow terms
    states' = fmap (ixMapping!) states

    extPtrMask = getExtPtrMask terms (elems states)

    swallow ix parentCount t
      | isRecursive (project t) =
          if parentCount > 1 || extPtrMask!ix then Keep else Swallow
      | otherwise = if extPtrMask!ix then Copy else Swallow


simplify :: Afa -> Afa
simplify afa@Afa{terms} = afa{terms=fmap (cata simplify_alg) terms}


costFixpoint :: (Afa -> Afa) -> Afa -> Afa
costFixpoint fn afa = fixpoint where
  iters = map (TreeDag.Utils.cost . terms &&& id)$ iterate fn afa
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


sortUniq :: (Afa.Prism.PositiveTerm f) => f Int -> f Int
sortUniq (Afa.Prism.And xs) = Afa.Prism.And$ map head$ group$ sort xs
sortUniq (Afa.Prism.Or xs) = Afa.Prism.Or$ map head$ group$ sort xs
sortUniq x = x

toArr :: [a] -> Array Int a
toArr xs = listArray (0, length xs - 1) xs

hashConsThenSwallow :: Afa -> Afa
hashConsThenSwallow afa@Afa{terms, states} = afa{terms = terms2, states = states2}
  where
  ixMapping1 :: Array Int Int
  (ixMapping1, toArr -> terms1) = runST$ runHashConsMonadT$
    cataScanM (treeDagCataScanMAlg$ hashCons' . sortUniq) terms >>= lift . unsafeFreeze

  states1 = fmap (ixMapping1!) states
  extPtrMask = getExtPtrMask terms1 (elems states1)

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
  qixMap = toArr$ scanl (\ix q -> if qixLit ix then ix else succ ix) 0$ elems states

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


-- | This function does not belong to this module
complement :: Afa -> Afa
complement afa@Afa{terms} = afa{terms = fmap Afa.TreeDag.complement terms}


data SimplificationResult
  = NonPositiveStates
  | EmptyLang
  | NonEmptyLang
  | UndecidedEmptiness Afa


preprocess :: Afa -> SimplificationResult
preprocess (removeOrphans . followRefs -> afa0@Afa{terms, states}) =
  case sequence$ elems$ Afa.TreeDag.makeStatesPositive terms of
    Nothing -> NonPositiveStates
    Just (listArray (bounds terms) -> terms')
      | all (nonNeg. fst . (terms'!))$ elems states ->
          closure$ afa0{terms = fmap snd terms'}
      | otherwise -> NonPositiveStates

  where
  closure afa0 =
    case removeFalseStates afa1 of
      Nothing -> EmptyLang
      Just afa2 -> case removeTrueStates afa2 of
        Nothing -> NonEmptyLang
        Just afa3
          | stateCount afa3 == stateCount afa1 -> UndecidedEmptiness afa3
          | otherwise -> closure afa3

    where
    afa1 = costFixpoint (simplify . hashConsThenSwallow)$ removeOrphans$ followRefs afa0

  stateCount = rangeSize . bounds . Afa.states

  nonNeg Afa.StatePositiveness.Negative = False
  nonNeg _ = True
