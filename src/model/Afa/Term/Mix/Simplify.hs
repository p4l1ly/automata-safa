{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Afa.Term.Mix.Simplify where

import Control.Arrow
import Control.RecursionSchemes.Lens
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
  (nonEmptyConcatMap, (>&>), nonemptyCanonicalizeWith, listArray', eixMappedGs)
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
    in maybe (Left True) (Right . Or)$ NE.nonEmpty ts3
  bt -> Right bt

-- PERF: use hashset
canonicalizeWith :: (Eq r, Ord r) => (t -> r) -> Term p q t -> Term p q t
canonicalizeWith getR (And ts) = And$ nonemptyCanonicalizeWith getR ts
canonicalizeWith getR (Or ts) = Or$ nonemptyCanonicalizeWith getR ts
canonicalizeWith _ x = x

simplify :: (Eq r, Hashable r, Ord r)
  => (t -> Term p q t)
  -> (t -> r)
  -> Term p q (Either Bool t) -> Either Bool (Either t (Term p q t))
simplify project getR =
  ( ( deLit
      >&> deUnary
          >&> flatten project >>> canonicalizeWith getR >>> absorb project getR
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
    (gs'M :: STArray s Int Any) <- unsafeThaw gs'
    (LiftArray ixMap'M, tList) <- runHashConsT$
      hyloScanTTerminal' traversed hylogebra (LiftArray gs'M)
    ixMap' <- unsafeFreeze ixMap'M
    return (fmap (>>= (ixMap'!) >&> fst) ixMap, listArray' tList)

  gs' = accumArray (\_ x -> x) mempty (bounds arr) (eixMappedGs ixMap gs)

  alg (Any False) _ = return$ error "accessing element without parents"
  alg _ t = case simplify (getCompose . unFix . snd) fst t of
    Left b -> return$ Left b
    Right (Left it) -> return$ Right it
    Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)

  hylogebra (g, i) = return ((g,) <$> arr!i, alg g)


simplifyDagUntilFixpoint :: forall p q. (Eq p, Hashable p, Eq q, Hashable q)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (Term p q Int))
  -> (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDagUntilFixpoint gs (ixMap, arr) =
  fromJust$ msum$ zipWith better iters (tail iters)
  where
  cost ts = (length ts, sum$ fmap length ts)
  iters = iterate
    ((cost . snd &&& id) . simplifyDag gs . snd)
    (cost arr, (ixMap, arr))
  better (c1, r) (c2, _) = r <$ guard (c1 <= c2)
