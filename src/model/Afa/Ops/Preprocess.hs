{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}

module Afa.Ops.Preprocess where

import Control.Arrow
import Data.List
import Data.Array
import Data.Array.Unsafe
import Control.Monad.ST
import Data.Foldable
import Control.Monad.Trans

import Data.Functor.Foldable
import Data.Functor.Foldable.Dag.Consing (hashCons', runHashConsMonadT)
import Data.Functor.Foldable.Dag.Monadic (cataScanM)
import Data.Functor.Foldable.Dag.Pure (cataScan)
import Data.Functor.Tree (treeFAlgM)
import qualified Data.Functor.Foldable.Dag.TreeNested as TreeDag
import Data.Functor.Foldable.Dag.TreeNested
  ( condenseTreesInTreeDag
  , condenseTreesInDag
  , Swallow(..)
  )
import qualified Data.Functor.Foldable.Dag.Utils as Dag.Utils

import Afa.Term.Prism.Ops.Simplify (simplify_alg)
import Afa.Term.Prism (isRecursive)
import Afa (Afa(Afa, terms, states))
import Afa.Term.TreeF (pattern Ref, Term, pattern LTrue, pattern LFalse, pattern State)
import qualified Afa.Term as T
import qualified Afa.Term.TreeFBase as TFB
import qualified Afa.Term.Prism as Prism
import Afa.Term.TreeF.Ops (makeStatesPositive)
import Afa.Term.Prism.Ops.StatePositiveness (StateSignum(Negative))

followRefs :: Afa -> Afa
followRefs afa@Afa{terms, states} = afa{states=fmap follow states} where
  follow ix = case terms!ix of Ref ix' -> follow ix'; _ -> ix

getExtPtrMask terms ptrs = array (bounds terms)$
  fmap (, False) (indices terms) ++ map (, True) ptrs

swallowOnlyChilds :: Afa -> Afa
swallowOnlyChilds afa@Afa{terms, states} = afa{terms = terms', states = states'}
  where
    (ixMapping, terms') = condenseTreesInTreeDag swallow terms
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
  iters = map (TreeDag.cost . terms &&& id)$ iterate fn afa
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


sortUniq :: (Prism.PositiveTerm f) => f Int -> f Int
sortUniq (Prism.And xs) = Prism.And$ map head$ group$ sort xs
sortUniq (Prism.Or xs) = Prism.Or$ map head$ group$ sort xs
sortUniq x = x

toArr :: [a] -> Array Int a
toArr xs = listArray (0, length xs - 1) xs

hashConsThenSwallow :: Afa -> Afa
hashConsThenSwallow afa@Afa{terms, states} = afa{terms = terms2, states = states2}
  where
  ixMapping1 :: Array Int Int
  (ixMapping1, toArr -> terms1) = runST$ runHashConsMonadT$
    cataScanM (treeFAlgM$ hashCons' . sortUniq) terms >>= lift . unsafeFreeze

  states1 = fmap (ixMapping1!) states
  extPtrMask = getExtPtrMask terms1 (elems states1)

  swallow ix parentCount t
    | isRecursive (project t) =
        if parentCount > 1 || extPtrMask!ix then Keep else Swallow
    | otherwise = if extPtrMask!ix then Copy else Swallow

  (ixMapping2, terms2) = condenseTreesInDag swallow terms1
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
    TFB.NRef (T.State ix)
      | qixLit ix -> lit
      | otherwise -> State$ qixMap!ix
    t -> embed t

  states' = listArray (0, length list - 1) list
    where list = map snd$ filter (not . qixLit . fst)$ assocs states


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


data SimplificationResult
  = NonPositiveStates
  | EmptyLang
  | NonEmptyLang
  | UndecidedEmptiness Afa
  deriving (Show, Eq)


preprocess :: Afa -> SimplificationResult
preprocess (removeOrphans . followRefs -> afa0@Afa{terms, states}) =
  case sequence$ elems$ makeStatesPositive terms of
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

  nonNeg Negative = False
  nonNeg _ = True
