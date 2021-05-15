{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Term.Mix.Simplify where

import Debug.Trace

import Data.Array.Base (unsafeRead, unsafeWrite, unsafeNewArray_)
import Control.Monad.Trans
import Data.Foldable
import Data.Traversable
import Control.Arrow
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.HashCons
import Control.Lens
import Data.Fix
import Data.Functor.Compose
import Data.Array.Unsafe
import Control.Monad.ST
import Data.Array.ST
import Data.Maybe
import Data.Array
import Control.Monad
import Data.Monoid (Endo(..), Any(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Hashable
import qualified Data.HashSet as S

import Afa.Lib
  ( nonEmptyConcatMap
  , (>&>)
  , nonemptyCanonicalizeWith
  , listArray'
  , eixMappedGs2
  , DumbCount(..)
  )
import Afa.Lib.LiftArray
import Afa.Term.Mix

deLit :: Term p q (Either Bool a) -> Either Bool (Term p q a)
deLit LTrue = Left True
deLit (Predicate p) = Right$ Predicate p
deLit (State q) = Right$ State q
deLit (And xs) = case xs' of
  Nothing -> Left False
  Just [] -> Left True
  Just (x:xs) -> Right$ And$ x :| xs
  where
  xs' = (`appEndo` Just [])$ flip foldMap xs$ \case
    Left True -> Endo id
    Left False -> Endo (const Nothing)
    Right a -> Endo ((a:) <$>)
deLit (Or xs) = case xs' of
  Nothing -> Left True
  Just [] -> Left False
  Just (x:xs) -> Right$ Or$ x :| xs
  where
  xs' = (`appEndo` Just [])$ flip foldMap xs$ \case
    Left False -> Endo id
    Left True -> Endo (const Nothing)
    Right a -> Endo ((a:) <$>)

deUnary :: Term p q t -> Either t (Term p q t)
deUnary = \case
  And (t :| []) -> Left t
  Or (t :| []) -> Left t
  bt -> Right bt

flatten :: (t -> Term p q t) -> Term p q t -> Term p q t
flatten project = \case
  And ts -> And$ flip nonEmptyConcatMap ts$ \t ->
    case project t of
      And ts2 -> ts2
      _ -> t :| []
  Or ts -> Or$ flip nonEmptyConcatMap ts$ \t ->
    case project t of
      Or ts2 -> ts2
      _ -> t :| []
  bt -> bt

flatten0 :: (t -> Maybe (Term p q t)) -> Term p q t -> Term p q t
flatten0 project = \case
  And ts -> And$ flip nonEmptyConcatMap ts$ \t ->
    case project t of
      Just (And ts2) -> ts2
      _ -> t :| []
  Or ts -> Or$ flip nonEmptyConcatMap ts$ \t ->
    case project t of
      Just (Or ts2) -> ts2
      _ -> t :| []
  bt -> bt

absorb :: (Eq r, Hashable r) => (t -> Term p q t) -> (t -> r)
  -> Term p q t -> Either Bool (Term p q t)
absorb project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          Or ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe (Left True) (Right . And)$ NE.nonEmpty ts3
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          And ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe (Left False) (Right . Or)$ NE.nonEmpty ts3
  bt -> Right bt

-- PERF: use hashset
canonicalizeWith :: (Eq r, Ord r) => (t -> r) -> Term p q t -> Term p q t
canonicalizeWith getR (And ts) = And$ nonemptyCanonicalizeWith getR ts
canonicalizeWith getR (Or ts) = Or$ nonemptyCanonicalizeWith getR ts
canonicalizeWith _ x = x

simplify :: (Eq r, Hashable r, Ord r)
  => (t -> (DumbCount, Term p q t))
  -> (t -> r)
  -> Term p q (Either Bool t) -> Either Bool (Either t (Term p q t))
simplify project getR =
  ( ( deLit
      >&> deUnary
          >&> flatten0 ((\case (Many, _) -> Nothing; (_, x) -> Just x) . project)
              >>> canonicalizeWith getR
              >>> absorb (snd . project) getR
    ) >>> skipJoin
  )
  >&> join . fmap deUnary
  where
  skipJoin (Right (Right (Left b))) = Left b
  skipJoin (Right (Right (Right t))) = Right (Right t)
  skipJoin (Left b) = Left b
  skipJoin (Right (Left t)) = Right (Left t)


simplifyDag :: forall p q. (Eq p, Hashable p, Eq q, Hashable q)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p q Int))
  -> (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDag gs (ixMap, arr) = runST action where
  action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p q Int))
  action = do
    (ixMap', tList) <- runHashConsT$ do
      gs'M :: STArray s Int DumbCount <- lift$ unsafeThaw$ eixMappedGs2 arr ixMap gs
      for_ [iend, iend - 1 .. ibeg]$ \i -> do
        g <- lift$ unsafeRead gs'M i
        for (arr!i)$ \ichild -> do
          gchild <- lift$ unsafeRead gs'M ichild
          lift$ unsafeWrite gs'M ichild$ gchild <> case g of Zero -> Zero; _ -> One

      ixMap'<- lift$ unsafeNewArray_ @(STArray s) bnds
      for_ [ibeg .. iend]$ \i -> do
        g <- lift$ unsafeRead gs'M i
        t <- for (arr!i)$ lift . unsafeRead ixMap'
        alg g t >>= lift . unsafeWrite ixMap' i

      lift$ unsafeFreeze ixMap'
    return (fmap (>>= (ixMap'!) >&> fst) ixMap, listArray' tList)

  bnds@(ibeg, iend) = bounds arr

  alg Zero _ = return$ error "accessing element without parents"
  alg g t = case simplify (\(_, Fix (Compose (Compose gt))) -> gt) fst t of
    Left b -> return$ Left b
    Right (Left it) -> return$ Right it
    Right (Right t) -> hashCons' (fmap fst t) <&> \i ->
      Right (i, Fix$Compose$Compose (g, t))


simplifyDagUntilFixpoint :: forall p q. (Eq p, Hashable p, Eq q, Hashable q)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p q Int))
  -> (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDagUntilFixpoint gs (ixMap, arr) =
  fromJust$ msum$ zipWith3 better iters tailIters (tail tailIters)
  where
  tailIters = tail iters
  cost ts = (rangeSize$ bounds ts, sum$ fmap length ts)
  iters = iterate
    ((cost . snd &&& id) . simplifyDag gs . snd)
    (cost arr, (ixMap, arr))
  better (c1, r) (c2, _) (c3, _) = r <$ guard (c1 <= c2 && c1 <= c3)
