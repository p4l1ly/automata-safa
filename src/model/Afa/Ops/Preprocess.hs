{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Ops.Preprocess
  ( -- followRefs
  -- , swallowOnlyChilds
  -- , simplify
  -- , costFixpoint
  -- , removeOrphans
  -- , hashConsThenSwallow
  -- , removeStatesBy
  -- , removeTrueStates
  -- , removeUnsatStates
  -- , SimplificationResult(..)
  )
  where

import Control.Arrow
import Data.List
import Data.Maybe
import Data.Array
import Data.Array.Unsafe
import Control.Monad.ST
import Data.Foldable
import Data.Hashable
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
import qualified Data.Functor.Foldable.MultiDag as MultiDag

-- import Afa.Term.Prism.Ops.Simplify (simplify_alg)
-- import Afa.Term.Prism (isRecursive)
import Afa (Afa(Afa, terms, states), TermLens, StateLens, Afa')
-- import Afa.Term.TreeF (pattern Ref, Term, pattern LTrue, pattern State, pattern Predicate)
-- import qualified Afa.Term as T
-- import qualified Afa.Term.TreeFBase as TFB
-- import qualified Afa.Term.Prism as Prism

followRefs :: Afa' p -> Afa' p
followRefs = MultiDag.followRefs @TermLens @StateLens

swallowOnlyChilds :: Afa' p -> Afa' p
swallowOnlyChilds = MultiDag.swallowOnlyChildsInTreeDag @StateLens @TermLens

remo :: Afa' p -> Afa' p
remo = MultiDag.removeOrphans @StateLens @TermLens

-- 
-- 
-- simplify :: Afa p -> Afa p
-- simplify afa@Afa{terms} = afa{terms=fmap (cata simplify_alg) terms}
-- 
-- 
-- costFixpoint :: (Afa p -> Afa p) -> Afa p -> Afa p
-- costFixpoint fn afa = fixpoint where
--   iters = map (TreeDag.cost . terms &&& id)$ iterate fn afa
--   Just ((_, fixpoint), _) =
--     find (\((c1, _), (c2, _)) -> c1 <= c2)$ zip iters (tail iters)
-- 
-- 
-- removeOrphans :: Afa p -> Afa p
-- removeOrphans afa@Afa{terms, states} =
--   afa{terms = terms', states = fmap (ixMapping!) states}
--   where
--     (ixMapping, terms') = Dag.Utils.removeOrphans$ accum
--       (\(a1, t) a2 -> (a1 || a2, t))
--       (fmap (False,) terms)
--       (map (, True)$ elems states)
-- 
-- 
-- sortUniq :: (Prism.PositiveTerm f) => f Int -> f Int
-- sortUniq (Prism.And xs) = Prism.And$ map head$ group$ sort xs
-- sortUniq (Prism.Or xs) = Prism.Or$ map head$ group$ sort xs
-- sortUniq x = x
-- 
-- 
-- toArr :: [a] -> Array Int a
-- toArr xs = listArray (0, length xs - 1) xs
-- 
-- 
-- hashConsThenSwallow :: (Eq p, Hashable p) => Afa p -> Afa p
-- hashConsThenSwallow afa@Afa{terms, states} = afa{terms = terms2, states = states2}
--   where
--   ixMapping1 :: Array Int Int
--   (ixMapping1, toArr -> terms1) = runST$ runHashConsMonadT$
--     cataScanM (treeFAlgM$ hashCons' . sortUniq) terms >>= lift . unsafeFreeze
-- 
--   states1 = fmap (ixMapping1!) states
--   extPtrMask = getExtPtrMask terms1 (elems states1)
-- 
--   swallow ix parentCount t
--     | isRecursive (project t) =
--         if parentCount > 1 || extPtrMask!ix then Keep else Swallow
--     | otherwise = if extPtrMask!ix then Copy else Swallow
-- 
--   (ixMapping2, terms2) = condenseTreesInDag swallow terms1
--   states2 = fmap (ixMapping2!) states1
-- 
-- 
-- removeStatesBy :: (Term p -> Maybe (Term p)) -> Afa p -> (Afa p, Maybe (Term p))
-- removeStatesBy replace afa@Afa{terms, states} =
--   (afa{terms = terms', states = states'}, replaceIx 0)
--   where
--   replaceIx ix = replace$ terms!(states!ix)
--   qixMap = listArray (bounds states)$ scanl succIfKept 0 [0..] where
--     succIfKept ix' ix = if isJust$ replaceIx ix then ix' else succ ix'
-- 
--   terms' = (`fmap` terms)$ cata$ \case
--     TFB.NRef (T.State ix) -> case replaceIx ix of
--       Just lit -> lit
--       Nothing -> State$ qixMap!ix
--     t -> embed t
-- 
--   states' = toArr$ map snd$ filter (not . isJust . replaceIx . fst)$ assocs states
-- 
-- 
-- -- | If Nothing is returned, the language of the Afa is universal.
-- -- | WARNING: this operation should not be applied before concatenation (and
-- -- | other operations where the length of the accepted word is relevant).
-- removeTrueStates :: Afa p -> Maybe (Afa p)
-- removeTrueStates afa = case q0sub of Nothing -> Just afa'; _ -> Nothing
--   where
--   (afa', q0sub) = flip removeStatesBy afa$ \case
--     LTrue -> Just LTrue
--     _ -> Nothing
-- 
-- 
-- -- | If Nothing is returned, the language of the Afa is empty.
-- -- | This operation should not affect anything negatively (contrary to
-- -- | removeTrueStates).
-- removeUnsatStates :: (p -> Bool) -> p -> Afa p -> Maybe (Afa p)
-- removeUnsatStates isSat replacement afa =
--   case q0sub of Nothing -> Just afa'; _ -> Nothing
--   where
--   (afa', q0sub) = flip removeStatesBy afa$ \case
--     Predicate (isSat -> False) -> Just$ Predicate replacement
--     _ -> Nothing
-- 
-- 
-- data SimplificationResult p
--   = EmptyLang
--   | NonEmptyLang
--   | UndecidedEmptiness (Afa p)
--   deriving (Show, Eq)


-- preprocess :: Afa p -> SimplificationResult
-- preprocess (followRefs >>> removeOrphans -> afa0@Afa{terms, states}) = closure afa0
--   where
--   closure afa0 =
--     case removeUnsatStates afa1 of
--       Nothing -> EmptyLang
--       Just afa2 -> case removeTrueStates afa2 of
--         Nothing -> NonEmptyLang
--         Just afa3
--           | stateCount afa3 == stateCount afa1 -> UndecidedEmptiness afa3
--           | otherwise -> closure afa3

--     where
--     afa1 = costFixpoint (simplify . hashConsThenSwallow)$ removeOrphans$ followRefs afa0

--   stateCount = rangeSize . bounds . Afa.states
