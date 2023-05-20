{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Term.Mix.Simplify where

import Debug.Trace

import Capability.Reader
import Capability.Sink
import Capability.Source
import Capability.State
import Control.Arrow hiding (first)
import Control.Lens
import Control.Monad
import Control.Monad.Free
import Control.Monad.Reader (ReaderT (..), ask)
import Control.Monad.ST
import Control.Monad.Trans
import Control.RecursionSchemes.Lens
import qualified Control.RecursionSchemes.Utils.HashCons2 as HCons
import Data.Array
import Data.Array.Base (unsafeAt, unsafeNewArray_, unsafeRead, unsafeWrite)
import Data.Array.ST
import Data.Array.Unsafe
import Data.Bifunctor
import Data.Fix
import Data.Foldable
import Data.Functor.Compose
import qualified Data.HashSet as S
import Data.Hashable
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Monoid (Any (..), Endo (..))
import Data.STRef
import Data.Traversable

import Afa.Lib (
  DumbCount (..),
  eixMappedGs2,
  listArray',
  nonEmptyConcatMap,
  nonemptyCanonicalizeWith,
  (>&>),
 )
import Afa.Lib.LiftArray
import Afa.Term.Mix

{-# INLINEABLE deLit #-}
deLit :: Term p q (Either Bool a) -> Either Bool (Term p q a)
deLit LTrue = Left True
deLit (Predicate p) = Right $ Predicate p
deLit (State q) = Right $ State q
deLit (And xs) = case xs' of
  Nothing -> Left False
  Just [] -> Left True
  Just (x : xs) -> Right $ And $ x :| xs
  where
    xs' = (`appEndo` Just []) $
      flip foldMap xs $ \case
        Left True -> Endo id
        Left False -> Endo (const Nothing)
        Right a -> Endo ((a :) <$>)
deLit (Or xs) = case xs' of
  Nothing -> Left True
  Just [] -> Left False
  Just (x : xs) -> Right $ Or $ x :| xs
  where
    xs' = (`appEndo` Just []) $
      flip foldMap xs $ \case
        Left False -> Endo id
        Left True -> Endo (const Nothing)
        Right a -> Endo ((a :) <$>)

{-# INLINEABLE deUnary #-}
deUnary :: Term p q t -> Either t (Term p q t)
deUnary = \case
  And (t :| []) -> Left t
  Or (t :| []) -> Left t
  bt -> Right bt

{-# INLINEABLE flatten #-}
flatten :: (t -> Term p q t) -> Term p q t -> Term p q t
flatten project = \case
  And ts -> And $
    flip nonEmptyConcatMap ts $ \t ->
      case project t of
        And ts2 -> ts2
        _ -> t :| []
  Or ts -> Or $
    flip nonEmptyConcatMap ts $ \t ->
      case project t of
        Or ts2 -> ts2
        _ -> t :| []
  bt -> bt

{-# INLINEABLE flatten0 #-}
flatten0 :: (t -> Maybe (Term p q t)) -> Term p q t -> Term p q t
flatten0 project = \case
  And ts -> And $
    flip nonEmptyConcatMap ts $ \t ->
      case project t of
        Just (And ts2) -> ts2
        _ -> t :| []
  Or ts -> Or $
    flip nonEmptyConcatMap ts $ \t ->
      case project t of
        Just (Or ts2) -> ts2
        _ -> t :| []
  bt -> bt

{-# INLINEABLE absorb #-}
absorb ::
  (Eq r, Hashable r) =>
  (t -> Term p q t) ->
  (t -> r) ->
  Term p q t ->
  Either Bool (Term p q t)
absorb project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 =
          flip NE.filter ts $
            project >>> \case
              Or ts2 -> not $ any (\t -> S.member (getR t) tsHash) ts2
              _ -> True
     in maybe (Left True) (Right . And) $ NE.nonEmpty ts3
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 =
          flip NE.filter ts $
            project >>> \case
              And ts2 -> not $ any (\t -> S.member (getR t) tsHash) ts2
              _ -> True
     in maybe (Left False) (Right . Or) $ NE.nonEmpty ts3
  bt -> Right bt

-- PERF: use hashset
{-# INLINEABLE canonicalizeWith #-}
canonicalizeWith :: (Eq r, Ord r) => (t -> r) -> Term p q t -> Term p q t
canonicalizeWith getR (And ts) = And $ nonemptyCanonicalizeWith getR ts
canonicalizeWith getR (Or ts) = Or $ nonemptyCanonicalizeWith getR ts
canonicalizeWith _ x = x

{-# INLINEABLE simplify #-}
simplify ::
  (Eq r, Hashable r, Ord r) =>
  (t -> (DumbCount, Term p q t)) ->
  (t -> r) ->
  Term p q (Either Bool t) ->
  Either Bool (Either t (Term p q t))
simplify project getR =
  ( ( deLit
        >&> deUnary
        >&> flatten0 ((\case (Many, _) -> Nothing; (_, x) -> Just x) . project)
          >>> canonicalizeWith getR
          >>> absorb (snd . project) getR
    )
      >>> skipJoin
  )
    >&> join . fmap deUnary
  where
    skipJoin (Right (Right (Left b))) = Left b
    skipJoin (Right (Right (Right t))) = Right (Right t)
    skipJoin (Left b) = Left b
    skipJoin (Right (Left t)) = Right (Left t)

simplify' ::
  (Eq r, Hashable r, Ord r) =>
  (t -> (DumbCount, Term p q t)) ->
  (t -> r) ->
  Term p q (Either Bool t) ->
  Either Bool (Free (Term p q) t)
simplify' project getR =
  simplify project getR >&> \case
    Left t -> Pure t
    Right term -> Free $ term <&> Pure

share ::
  (Eq r, Hashable r, Ord r) =>
  (t -> (DumbCount, Term p q t)) ->
  (t -> r) ->
  Term p q (Either Bool t) ->
  Either Bool (Free (Term p q) t)
share project getR t = fmap Free $
  for t $ \case
    Left False -> Left False
    Left True -> Right $ Free LTrue
    Right t -> Right $ Pure t

type BuilderCtx s x = STRef s (HCons.ConsState x x)
newtype Builder s x a = Builder {runBuilder :: BuilderCtx s x -> ST s a}
  deriving (Functor, Applicative, Monad) via (ReaderT (BuilderCtx s x) (ST s))
  deriving
    ( HasState "cons" (HCons.ConsState x x)
    , HasSource "cons" (HCons.ConsState x x)
    , HasSink "cons" (HCons.ConsState x x)
    )
    via ReaderRef (MonadReader (ReaderT (BuilderCtx s x) (ST s)))
blift = Builder . const

{-# INLINEABLE delitDag #-}
delitDag ::
  forall p q.
  Array Int (Term p q Int) ->
  (Array Int (Either Bool Int), Array Int (Term p q Int))
delitDag arr = runST action
  where
    bnds@(ibeg, iend) = bounds arr

    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p q Int))
    action = do
      stateV <- newSTRef (0, [])
      ixMap' <- flip runReaderT stateV $ do
        ixMap' <- lift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          t <- lift $ for (arr `unsafeAt` i) $ unsafeRead ixMap'
          alg t >>= lift . unsafeWrite ixMap' i
        lift $ unsafeFreeze ixMap'
      (_, terms) <- readSTRef stateV
      return (ixMap', listArray (0, length terms - 1) $ reverse terms)

    alg ::
      forall s.
      Term p q (Either Bool Int) ->
      ReaderT (STRef s (Int, [Term p q Int])) (ST s) (Either Bool Int)
    alg t = case deLit t <&> deUnary of
      Left b -> return $ Left b
      Right (Left ix) -> return $ Right ix
      Right (Right t) ->
        Right <$> do
          stateV <- Control.Monad.Reader.ask
          (i, xs) <- lift $ readSTRef stateV
          lift $ writeSTRef stateV (i + 1, t : xs)
          return i

{-# INLINEABLE simplifyDag #-}
simplifyDag ::
  forall p q.
  (Eq p, Hashable p, Eq q, Hashable q) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p q Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDag gs (ixMap, arr) = runST action
  where
    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p q Int))
    action = do
      hcref <- newSTRef HCons.consState0
      ixMap' <- flip runBuilder hcref $ do
        gs'M :: STArray s Int DumbCount <- blift $ unsafeThaw $ eixMappedGs2 arr ixMap gs
        blift $
          for_ [iend, iend - 1 .. ibeg] $ \i -> do
            g <- unsafeRead gs'M i
            for (arr `unsafeAt` i) $ \ichild -> do
              gchild <- unsafeRead gs'M ichild
              unsafeWrite gs'M ichild $ gchild <> case g of Zero -> Zero; _ -> One

        ixMap' <- blift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          g <- blift $ unsafeRead gs'M i
          t <- blift $ for (arr `unsafeAt` i) $ unsafeRead ixMap'
          alg g t >>= blift . unsafeWrite ixMap' i

        blift $ unsafeFreeze ixMap'

      (tListSize, tList) <- HCons.consResult <$> readSTRef hcref
      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray (0, tListSize - 1) tList)

    bnds@(ibeg, iend) = bounds arr

    alg Zero _ = return $ error "accessing element without parents"
    alg g t = case simplify (\(_, Fix (Compose (Compose gt))) -> gt) fst t of
      Left b -> return $ Left b
      Right (Left it) -> return $ Right it
      Right (Right t) ->
        HCons.cons @"cons" (fmap fst t) <&> \i ->
          Right (i, Fix $ Compose $ Compose (g, t))

{-# INLINEABLE simplifyDag3 #-}
simplifyDag3 ::
  forall p q.
  (Eq p, Hashable p, Eq q, Hashable q) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p q Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDag3 gs (ixMap, arr) = runST action
  where
    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p q Int))
    action = do
      hcref <- newSTRef HCons.consState0
      ixMap' <- flip runBuilder hcref $ do
        gs'M :: STArray s Int DumbCount <- blift $ unsafeThaw $ eixMappedGs2 arr ixMap gs
        blift $
          for_ [iend, iend - 1 .. ibeg] $ \i -> do
            g <- unsafeRead gs'M i
            for (arr `unsafeAt` i) $ \ichild -> do
              gchild <- unsafeRead gs'M ichild
              unsafeWrite gs'M ichild $ gchild <> case g of Zero -> Zero; _ -> One

        ixMap' <- blift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          g <- blift $ unsafeRead gs'M i
          t <- blift $ for (arr `unsafeAt` i) $ fmap (first fst) . unsafeRead ixMap'
          alg g t >>= blift . unsafeWrite ixMap' i

        fmap (fmap keepLits) $ blift $ unsafeFreeze ixMap'

      (tListSize, tList) <- HCons.consResult <$> readSTRef hcref
      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray (0, tListSize - 1) tList)

    keepLits (Left (True, i)) = Right (i, undefined)
    keepLits (Left (False, _)) = Left False
    keepLits (Right t) = Right t

    bnds@(ibeg, iend) = bounds arr

    alg Zero _ = return $ error "accessing element without parents"
    alg g t = case simplify (\(_, Fix (Compose (Compose gt))) -> gt) fst t of
      Left True -> HCons.cons @"cons" LTrue <&> Left . (True,)
      Left b -> return $ Left (b, undefined)
      Right (Left it) -> return $ Right it
      Right (Right t) ->
        HCons.cons @"cons" (fmap fst t) <&> \i ->
          Right (i, Fix $ Compose $ Compose (g, t))

{-# INLINEABLE simplifyDag4 #-}
simplifyDag4 ::
  forall p q.
  (Eq p, Hashable p, Eq q, Hashable q) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p q Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDag4 gs (ixMap, arr) = runST action
  where
    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p q Int))
    action = do
      hcref <- newSTRef HCons.consState0
      ixMap' <- flip runBuilder hcref $ do
        gs'M :: STArray s Int DumbCount <- blift $ unsafeThaw $ eixMappedGs2 arr ixMap gs
        blift $
          for_ [iend, iend - 1 .. ibeg] $ \i -> do
            g <- unsafeRead gs'M i
            for (arr `unsafeAt` i) $ \ichild -> do
              gchild <- unsafeRead gs'M ichild
              unsafeWrite gs'M ichild $ gchild <> case g of Zero -> Zero; _ -> One

        ixMap' <- blift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          g <- blift $ unsafeRead gs'M i
          t <- blift $ for (arr `unsafeAt` i) $ unsafeRead ixMap'
          alg g t >>= blift . unsafeWrite ixMap' i

        blift $ unsafeFreeze ixMap'

      (tListSize, tList) <- HCons.consResult <$> readSTRef hcref
      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray (0, tListSize - 1) tList)

    bnds@(ibeg, iend) = bounds arr

    alg Zero _ = return $ error "accessing element without parents"
    alg g t = case share (\(_, Fix (Compose (Compose gt))) -> gt) fst t of
      Left b -> return $ Left b
      Right x -> fmap Right $
        flip iterM x $ \t -> do
          t' <- sequence t
          i <- HCons.cons @"cons" (fmap fst t')
          return (i, Fix $ Compose $ Compose (g, t'))

-- -- more elegant but slower, don't know exactly why (probably some inlining + specialization issues)
-- {-# INLINABLE simplifyDag2 #-}
-- simplifyDag2 :: forall p q. (Eq p, Hashable p, Eq q, Hashable q)
--   => Array Int Any
--   -> (Array Int (Either Bool Int), Array Int (Term p q Int))
--   -> (Array Int (Either Bool Int), Array Int (Term p q Int))
-- simplifyDag2 gs (ixMap, arr) = runST action where
--   action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p q Int))
--   action = do
--     (ixMap', tList) <- runHashConsT$ do
--       gs'M :: LSTArray s Int DumbCount <- unsafeThaw$ eixMappedGs2 arr ixMap gs
--       (_, ixMap') <- hyloScanTFast @(LSTArray s) (return ())
--         (\g i -> for_ (arr `unsafeAt` i)$ \ichild -> do
--           gchild <- unsafeRead gs'M ichild
--           unsafeWrite gs'M ichild$ gchild <> case g of Zero -> Zero; _ -> One
--         )
--         (\ixMap' _ g i -> for (arr `unsafeAt` i) (unsafeRead ixMap') >>= alg g)
--         gs'M
--
--       unsafeFreeze ixMap'
--     return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray' tList)
--
--   bnds@(ibeg, iend) = bounds arr
--
--   alg Zero _ = return$ error "accessing element without parents"
--   alg g t = case simplify (\(_, Fix (Compose (Compose gt))) -> gt) fst t of
--     Left b -> return$ Left b
--     Right (Left it) -> return$ Right it
--     Right (Right t) -> hashCons' (fmap fst t) <&> \i ->
--       Right (i, Fix$Compose$Compose (g, t))

{-# INLINEABLE simplifyDagUntilFixpoint #-}
simplifyDagUntilFixpoint ::
  forall p q.
  (Eq p, Hashable p, Eq q, Hashable q) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p q Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p q Int))
simplifyDagUntilFixpoint gs (ixMap, arr) =
  fromJust $ msum $ zipWith3 better iters tailIters (tail tailIters)
  where
    tailIters = tail iters
    cost ts = (rangeSize $ bounds ts, sum $ fmap length ts)
    iters =
      iterate
        ((cost . snd &&& id) . simplifyDag gs . snd)
        (cost arr, (ixMap, arr))
    better (c1, r) (c2, _) (c3, _) = r <$ guard (c1 <= c2 && c1 <= c3)
