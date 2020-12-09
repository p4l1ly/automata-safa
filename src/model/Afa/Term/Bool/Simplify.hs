{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Afa.Term.Bool.Simplify where

import Control.Arrow
import Control.RecursionSchemes.Lens
import Control.Lens
import Data.Fix
import Data.Functor.Compose
import Data.Array
import Data.Array.Unsafe
import Control.Monad.ST
import Data.Array.ST
import Data.Maybe
import Control.Monad
import Data.Monoid (Endo(..), Any(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Hashable
import qualified Data.HashSet as S

import Afa.Lib
  (nonEmptyConcatMap, (>&>), nonemptyCanonicalizeWith, listArray', eixMappedGs)
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

canonicalize :: (Eq r, Ord r) => (t -> r) -> Term p t -> Term p t
canonicalize getR (And ts) = And$ nonemptyCanonicalizeWith getR ts
canonicalize getR (Or ts) = Or$ nonemptyCanonicalizeWith getR ts
canonicalize _ x = x

simplify :: (Eq r, Hashable r, Ord r)
  => (t -> Term p t)
  -> (t -> r)
  -> Term p (Either Bool t) -> Either Bool (Either t (Term p t))
simplify project getR =
  ( ( deLit
      >&> deUnary
      >=> ( deNotNot project
            >&> flatten project
                >>> canonicalize getR
                >>> absorb project getR
                >>> complementLaws project getR
          )
    ) >>> skipJoin
  )
  >&> join . fmap deUnary
  where
  skipJoin (Right (Right (Left b))) = Left b
  skipJoin (Right (Right (Right t))) = Right (Right t)
  skipJoin (Left b) = Left b
  skipJoin (Right (Left t)) = Right (Left t)


simplifyDag :: forall p. (Eq p, Hashable p)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDag gs (ixMap, arr) = runST action where
  action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p Int))
  action = do
    (gs'M :: STArray s Int Any) <- unsafeThaw$ eixMappedGs arr ixMap gs
    (LiftArray ixMap'M, tList) <- runHashConsT$
      hyloScanTTerminal' traversed hylogebra (LiftArray gs'M)
    ixMap' <- unsafeFreeze ixMap'M
    return (fmap (>>= (ixMap'!) >&> fst) ixMap, listArray' tList)

  alg (Any False) _ = return$ error "accessing element without parents"
  alg _ t = case simplify (getCompose . unFix . snd) fst t of
    Left b -> return$ Left b
    Right (Left it) -> return$ Right it
    Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)

  hylogebra (g, i) = return ((g,) <$> arr!i, alg g)


simplifyDagUntilFixpoint :: forall p. (Eq p, Hashable p)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
  -> (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDagUntilFixpoint gs (ixMap, arr) =
  fromJust$ msum$ zipWith better iters (tail iters)
  where
  cost ts = (length ts, sum$ fmap length ts)
  iters = iterate
    ((cost . snd &&& id) . simplifyDag gs . snd)
    (cost arr, (ixMap, arr))
  better (c1, r) (c2, _) = r <$ guard (c1 <= c2)
