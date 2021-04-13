{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Afa.Term.Bool.Simplify where

import Control.Monad.Free
import Control.Arrow
import Control.RecursionSchemes.Lens
import Control.Lens
import Data.Fix
import Data.Functor.Compose
import Data.Array
import Data.Array.Unsafe
import Control.Monad.ST
import Data.Maybe
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
import Afa.Term.Bool


deLit :: Term p (Either Bool a) -> Either Bool (Term p a)
deLit LTrue = Left True
deLit LFalse = Left False
deLit (Predicate p) = Right$ Predicate p
deLit (Not (Left b)) = Left$ not b
deLit (Not (Right x)) = Right$ Not x
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

deUnary :: Term p t -> Either t (Term p t)
deUnary = \case
  And (t :| []) -> Left t
  Or (t :| []) -> Left t
  bt -> Right bt

deNotNot :: (t' -> Term p t) -> Term p t' -> Either t (Term p t')
deNotNot project = \case
  bt@(Not t) -> case project t of
    Not t -> Left t
    _ -> Right bt
  bt -> Right bt

flatten :: (t -> Term p t) -> Term p t -> Term p t
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

flatten0 :: (t -> Maybe (Term p t)) -> Term p t -> Term p t
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

-- PERF: use list? radix grouping?
absorb :: (Eq r, Hashable r) => (t -> Term p t) -> (t -> r) -> Term p t -> Term p t
absorb project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          Or ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe LTrue And$ NE.nonEmpty ts3
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 = flip NE.filter ts$ project >>> \case
          And ts2 -> not$ any (\t -> S.member (getR t) tsHash) ts2
          _ -> True
    in maybe LFalse Or$ NE.nonEmpty ts3
  bt -> bt

-- PERF: use list? radix grouping?
complementLaws :: (Eq r, Hashable r)
  => (t -> Term p t) -> (t -> r) -> Term p t -> Either Bool (Term p t)
complementLaws project getR x = case x of
  (And ts) -> if hasCompl ts then Left False else Right x
  (Or ts) -> if hasCompl ts then Left True else Right x
  _ -> Right x
  where
  hasCompl (NE.toList -> ts) = any ((`S.member` nots) . getR) ts where
    nots = S.fromList$
      mapMaybe (project >>> \case Not t -> Just$ getR t; _ -> Nothing) ts

commonIdentities :: (Eq r, Hashable r)
  => (t -> (DumbCount, Term p t))
  -> (t -> r)
  -> Term p t
  -> Either Bool (Free (Term p) t)
commonIdentities project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        removeCommon x = case snd$ project x of
          Not x' | getR x' `S.member` tsHash -> Nothing
          _ -> Just x
        ts' = ts <&> \x -> case project x of
          (One, Or (NE.toList >>> map removeCommon -> cts))
            | any isNothing cts ->
                maybe (Left False) (Right . Free . Or)$ NE.nonEmpty$ map Pure cts'
            | otherwise -> Right$ Pure x
            where cts' = catMaybes cts
          _ -> Right$ Pure x
    in Free . And <$> sequence ts'
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        removeCommon x = case snd$ project x of
          Not x' | getR x' `S.member` tsHash -> Nothing
          _ -> Just x
        ts' = ts <&> \x -> case project x of
          (One, And (NE.toList >>> map removeCommon -> cts))
            | any isNothing cts ->
                maybe (Left True) (Right . Free . And)$ NE.nonEmpty$ map Pure cts'
            | otherwise -> Right$ Pure x
            where cts' = catMaybes cts
          _ -> Right$ Pure x
    in Free . Or <$> sequence ts'
  x -> Right$ Free$ Pure <$> x

canonicalize :: (Eq r, Ord r) => (t -> r) -> Term p t -> Term p t
canonicalize getR (And ts) = And$ nonemptyCanonicalizeWith getR ts
canonicalize getR (Or ts) = Or$ nonemptyCanonicalizeWith getR ts
canonicalize _ x = x

simplify :: forall p r t. (Eq r, Hashable r, Ord r)
  => (t -> (DumbCount, Term p t))
  -> (t -> r)
  -> Term p (Either Bool t) -> Either Bool (Free (Term p) t)
simplify project getR = stage1 >&> fmap pure >>> iter (either id Free . deUnary)
  where
  skipJoin (Right (Right (Left b))) = Left b
  skipJoin (Right (Right (Right t))) = Right t
  skipJoin (Left b) = Left b
  skipJoin (Right (Left t)) = Right$ Pure t

  stage1 :: Term p (Either Bool t) -> Either Bool (Free (Term p) t)
  stage1 =
    ( deLit
      >&> deUnary
      >=> ( deNotNot (snd . project)
            >&> flatten0 ((\case (Many, _) -> Nothing; (_, x) -> Just x) . project)
                >>> canonicalize getR
                >>> absorb (snd . project) getR
                >>> ( complementLaws (snd . project) getR
                      >&> commonIdentities project getR
                    )
                >>> join
          )
    ) >>> skipJoin


simplifyDag :: forall p. (Eq p, Hashable p)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDag gs (ixMap, arr) = runST action where
  action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p Int))
  action = do
    (ixMap', tList) <- runHashConsT$ do
      (gs'M :: LSTArray s Int DumbCount) <- unsafeThaw$ eixMappedGs2 arr ixMap gs
      unsafeFreeze =<< hyloScanTTerminal' traversed hylogebra gs'M
    return (fmap (>>= (ixMap'!) >&> fst) ixMap, listArray' tList)

  alg Zero _ = return$ error "accessing element without parents"
  alg g t = case simplify (\(_, Fix (Compose (Compose gt))) -> gt) fst t of
    Left b -> return$ Left b
    Right x -> fmap Right$ flip iterM x$ \t -> do
      t' <- sequence t
      i <- hashCons' (fmap fst t')
      return (i, Fix$Compose$Compose (g, t'))

  hylogebra (g, i) = return ((gchild,) <$> arr!i, alg g)
    where gchild = case g of Zero -> Zero; _ -> One


simplifyDagUntilFixpoint :: forall p. (Eq p, Hashable p)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDagUntilFixpoint gs (ixMap, arr) =
  fromJust$ msum$ zipWith3 better iters tailIters (tail tailIters)
  where
  tailIters = tail iters
  cost ts = (rangeSize$ bounds ts, sum$ fmap length ts)
  iters = iterate
    ((cost . snd &&& id) . simplifyDag gs . snd)
    (cost arr, (ixMap, arr))
  better (c1, r) (c2, _) (c3, _) = r <$ guard (c1 <= c2 && c1 <= c3)
