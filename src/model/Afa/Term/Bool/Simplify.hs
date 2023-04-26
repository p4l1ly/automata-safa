{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Term.Bool.Simplify where

import Capability.Reader hiding (Pos)
import Capability.Sink hiding (Pos)
import Capability.Source hiding (Pos)
import Capability.State hiding (Pos)
import Control.Arrow hiding (first)
import Control.Lens
import Control.Monad
import Control.Monad.Free
import Control.Monad.Reader (ReaderT (..))
import qualified Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.Trans
import Control.RecursionSchemes.Lens
import qualified Control.RecursionSchemes.Utils.HashCons2 as HCons
import qualified Control.RecursionSchemes.Utils.NoCons2 as NoCons
import Data.Array
import Data.Array.Base (unsafeAt, unsafeNewArray_, unsafeRead, unsafeWrite)
import Data.Array.ST
import Data.Array.Unsafe
import Data.Bifunctor
import Data.Fix
import Data.Foldable
import Data.Functor.Compose
import qualified Data.HashMap.Strict as HM
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
import Afa.Term.Bool

{-# INLINEABLE deLit #-}
deLit :: Term p (Either Bool a) -> Either Bool (Term p a)
deLit LTrue = Left True
deLit LFalse = Left False
deLit (Predicate p) = Right $ Predicate p
deLit (Not (Left b)) = Left $ not b
deLit (Not (Right x)) = Right $ Not x
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
deUnary :: Term p t -> Either t (Term p t)
deUnary = \case
  And (t :| []) -> Left t
  Or (t :| []) -> Left t
  bt -> Right bt

{-# INLINEABLE deNotNot #-}
deNotNot :: (t' -> Term p t) -> Term p t' -> Either t (Term p t')
deNotNot project = \case
  bt@(Not t) -> case project t of
    Not t -> Left t
    _ -> Right bt
  bt -> Right bt

{-# INLINEABLE flatten #-}
flatten :: (t -> Term p t) -> Term p t -> Term p t
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
flatten0 :: (t -> Maybe (Term p t)) -> Term p t -> Term p t
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

-- PERF: use list? radix grouping?
{-# INLINEABLE absorb #-}
absorb :: (Eq r, Hashable r) => (t -> Term p t) -> (t -> r) -> Term p t -> Term p t
absorb project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 =
          flip NE.filter ts $
            project >>> \case
              Or ts2 -> not $ any (\t -> S.member (getR t) tsHash) ts2
              _ -> True
     in maybe LTrue And $ NE.nonEmpty ts3
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        ts3 =
          flip NE.filter ts $
            project >>> \case
              And ts2 -> not $ any (\t -> S.member (getR t) tsHash) ts2
              _ -> True
     in maybe LFalse Or $ NE.nonEmpty ts3
  bt -> bt

-- PERF: use list? radix grouping?
{-# INLINEABLE complementLaws #-}
complementLaws ::
  (Eq r, Hashable r) =>
  (t -> Term p t) ->
  (t -> r) ->
  Term p t ->
  Either Bool (Term p t)
complementLaws project getR x = case x of
  (And ts) -> if hasCompl ts then Left False else Right x
  (Or ts) -> if hasCompl ts then Left True else Right x
  _ -> Right x
  where
    hasCompl (NE.toList -> ts) = any ((`S.member` nots) . getR) ts
      where
        nots =
          S.fromList $
            mapMaybe (project >>> \case Not t -> Just $ getR t; _ -> Nothing) ts

{-# INLINEABLE commonIdentities #-}
commonIdentities ::
  (Eq r, Hashable r) =>
  (t -> (DumbCount, Term p t)) ->
  (t -> r) ->
  Term p t ->
  Either Bool (Free (Term p) t)
commonIdentities project getR = \case
  And ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        removeCommon x = case snd $ project x of
          Not x' | getR x' `S.member` tsHash -> Nothing
          _ -> Just x
        ts' =
          ts <&> \x -> case project x of
            (One, Or (NE.toList >>> map removeCommon -> cts))
              | any isNothing cts ->
                maybe (Left False) (Right . Free . Or) $ NE.nonEmpty $ map Pure cts'
              | otherwise -> Right $ Pure x
              where
                cts' = catMaybes cts
            _ -> Right $ Pure x
     in Free . And <$> sequence ts'
  Or ts ->
    let tsHash = foldl (flip S.insert) S.empty (getR <$> ts)
        removeCommon x = case snd $ project x of
          Not x' | getR x' `S.member` tsHash -> Nothing
          _ -> Just x
        ts' =
          ts <&> \x -> case project x of
            (One, And (NE.toList >>> map removeCommon -> cts))
              | any isNothing cts ->
                maybe (Left True) (Right . Free . And) $ NE.nonEmpty $ map Pure cts'
              | otherwise -> Right $ Pure x
              where
                cts' = catMaybes cts
            _ -> Right $ Pure x
     in Free . Or <$> sequence ts'
  x -> Right $ Free $ Pure <$> x

{-# INLINEABLE canonicalize #-}
canonicalize :: (Eq r, Ord r) => (t -> r) -> Term p t -> Term p t
canonicalize getR (And ts) = And $ nonemptyCanonicalizeWith getR ts
canonicalize getR (Or ts) = Or $ nonemptyCanonicalizeWith getR ts
canonicalize _ x = x

{-# INLINEABLE simplify #-}
simplify ::
  forall p r t.
  (Eq r, Hashable r, Ord r) =>
  (t -> (DumbCount, Term p t)) ->
  (t -> r) ->
  Term p (Either Bool t) ->
  Either Bool (Free (Term p) t)
simplify project getR = stage1 >&> fmap pure >>> iter (either id Free . deUnary)
  where
    skipJoin (Right (Right (Left b))) = Left b
    skipJoin (Right (Right (Right t))) = Right t
    skipJoin (Left b) = Left b
    skipJoin (Right (Left t)) = Right $ Pure t

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
      )
        >>> skipJoin

share ::
  (Eq r, Hashable r, Ord r) =>
  (t -> (DumbCount, Term p t)) ->
  (t -> r) ->
  Term p (Either Bool t) ->
  Either Bool (Free (Term p) t)
share project getR t = fmap Free $
  for t $ \case
    Left False -> Right $ Free LFalse
    Left True -> Right $ Free LTrue
    Right t -> Right $ Pure t

data RefSign = NoRefSign | Neg | Pos | NegPos deriving (Eq, Show)
instance Semigroup RefSign where
  NoRefSign <> x = x
  Neg <> Pos = NegPos
  Pos <> Neg = NegPos
  NegPos <> _ = NegPos
  _ <> NegPos = NegPos
  Neg <> Neg = Neg
  Pos <> Pos = Pos
  x <> NoRefSign = x

negRefSign Neg = Pos
negRefSign Pos = Neg
negRefSign x = x

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
  forall p.
  Array Int (Term p Int) ->
  (Array Int (Either Bool Int), Array Int (Term p Int))
delitDag arr = runST action
  where
    bnds@(ibeg, iend) = bounds arr

    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p Int))
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
      Term p (Either Bool Int) ->
      ReaderT (STRef s (Int, [Term p Int])) (ST s) (Either Bool Int)
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
  forall p.
  (Eq p, Hashable p) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDag gs (ixMap, arr) = runST action
  where
    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p Int))
    action = do
      hcref <- newSTRef HCons.consState0
      ixMap' <- flip runBuilder hcref $ do
        gs'M :: STArray s Int (DumbCount, RefSign) <- blift $ unsafeThaw gs''
        blift $
          for_ [iend, iend - 1 .. ibeg] $ \i -> do
            (count, sgn) <- unsafeRead gs'M i
            let node = arr `unsafeAt` i
            let count' = case count of Zero -> Zero; _ -> One
            let sgn' = case node of Not _ -> negRefSign sgn; _ -> sgn
            for (arr `unsafeAt` i) $ \ichild -> do
              gchild <- unsafeRead gs'M ichild
              unsafeWrite gs'M ichild $ gchild <> (count', sgn')

        gs3 :: Array Int (DumbCount, RefSign) <- blift $ unsafeFreeze gs'M
        -- WARNING, TODO: this can be applied only for variable predicates
        let predicateSigns =
              HM.fromListWith (<>) $
                catMaybes $
                  zipWith
                    (\(_, sgn) -> \case Predicate i -> Just (i, sgn); _ -> Nothing)
                    (elems gs3)
                    (elems arr)
            arr' =
              arr <&> \case
                x@(Predicate i) -> case predicateSigns HM.! i of
                  Neg -> LFalse
                  Pos -> LTrue
                  _ -> x
                x -> x

        ixMap' <- blift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          t <- blift $ for (arr' `unsafeAt` i) $ unsafeRead ixMap'
          alg (fst $ gs3 `unsafeAt` i) t >>= blift . unsafeWrite ixMap' i

        blift $ unsafeFreeze ixMap'

      (tListSize, tList) <- HCons.consResult <$> readSTRef hcref
      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray (0, tListSize - 1) tList)

    gs' = eixMappedGs2 arr ixMap gs
    gs'' = gs' <&> \case Zero -> (Zero, NoRefSign); x -> (x, Pos)
    bnds@(ibeg, iend) = bounds arr

    alg Zero _ = return $ error "accessing element without parents"
    alg count t = case simplify descend fst t of
      Left b -> return $ Left b
      Right x -> fmap Right $
        flip iterM x $ \t -> do
          t' <- sequence t
          i <- HCons.cons @"cons" (fmap fst t')
          return (i, Fix $ Compose $ Compose (count, t'))
      where
        descend (_, Fix (Compose (Compose gt))) = gt

{-# INLINEABLE simplifyDag3 #-}
simplifyDag3 ::
  forall p.
  (Eq p, Hashable p) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDag3 gs (ixMap, arr) = runST action
  where
    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p Int))
    action = do
      hcref <- newSTRef HCons.consState0
      ixMap' <- flip runBuilder hcref $ do
        gs'M :: STArray s Int (DumbCount, RefSign) <- blift $ unsafeThaw gs''
        blift $
          for_ [iend, iend - 1 .. ibeg] $ \i -> do
            (count, sgn) <- unsafeRead gs'M i
            let node = arr `unsafeAt` i
            let count' = case count of Zero -> Zero; _ -> One
            let sgn' = case node of Not _ -> negRefSign sgn; _ -> sgn
            for (arr `unsafeAt` i) $ \ichild -> do
              gchild <- unsafeRead gs'M ichild
              unsafeWrite gs'M ichild $ gchild <> (count', sgn')

        gs3 :: Array Int (DumbCount, RefSign) <- blift $ unsafeFreeze gs'M
        -- WARNING, TODO: this can be applied only for variable predicates
        let predicateSigns =
              HM.fromListWith (<>) $
                catMaybes $
                  zipWith
                    (\(_, sgn) -> \case Predicate i -> Just (i, sgn); _ -> Nothing)
                    (elems gs3)
                    (elems arr)
            arr' =
              arr <&> \case
                x@(Predicate i) -> case predicateSigns HM.! i of
                  Neg -> LFalse
                  Pos -> LTrue
                  _ -> x
                x -> x

        ixMap' <- blift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          t <- blift $ for (arr' `unsafeAt` i) $ fmap (first fst) . unsafeRead ixMap'
          alg (fst $ gs3 `unsafeAt` i) t >>= blift . unsafeWrite ixMap' i

        fmap (fmap keepLits) $ blift $ unsafeFreeze ixMap'

      (tListSize, tList) <- HCons.consResult <$> readSTRef hcref
      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray (0, tListSize - 1) tList)

    keepLits (Left (True, i)) = Right (i, undefined)
    keepLits (Left (False, _)) = Left False
    keepLits (Right t) = Right t

    gs' = eixMappedGs2 arr ixMap gs
    gs'' = gs' <&> \case Zero -> (Zero, NoRefSign); x -> (x, Pos)
    bnds@(ibeg, iend) = bounds arr

    alg Zero _ = return $ error "accessing element without parents"
    alg count t = case simplify descend fst t of
      Left True -> HCons.cons @"cons" LTrue <&> Left . (True,)
      Left b -> return $ Left (b, undefined)
      Right x -> fmap Right $
        flip iterM x $ \t -> do
          t' <- sequence t
          i <- HCons.cons @"cons" (fmap fst t')
          return (i, Fix $ Compose $ Compose (count, t'))
      where
        descend (_, Fix (Compose (Compose gt))) = gt

{-# INLINEABLE simplifyDag4 #-}
simplifyDag4 ::
  forall p.
  (Eq p, Hashable p) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p Int))
simplifyDag4 gs (ixMap, arr) = runST action
  where
    action :: forall s. ST s (Array Int (Either Bool Int), Array Int (Term p Int))
    action = do
      hcref <- newSTRef HCons.consState0
      ixMap' <- flip runBuilder hcref $ do
        gs'M :: STArray s Int (DumbCount, RefSign) <- blift $ unsafeThaw gs''
        blift $
          for_ [iend, iend - 1 .. ibeg] $ \i -> do
            (count, sgn) <- unsafeRead gs'M i
            let node = arr `unsafeAt` i
            let count' = case count of Zero -> Zero; _ -> One
            let sgn' = case node of Not _ -> negRefSign sgn; _ -> sgn
            for (arr `unsafeAt` i) $ \ichild -> do
              gchild <- unsafeRead gs'M ichild
              unsafeWrite gs'M ichild $ gchild <> (count', sgn')

        gs3 :: Array Int (DumbCount, RefSign) <- blift $ unsafeFreeze gs'M
        -- WARNING, TODO: this can be applied only for variable predicates
        let predicateSigns =
              HM.fromListWith (<>) $
                catMaybes $
                  zipWith
                    (\(_, sgn) -> \case Predicate i -> Just (i, sgn); _ -> Nothing)
                    (elems gs3)
                    (elems arr)
            arr' =
              arr <&> \case
                x@(Predicate i) -> case predicateSigns HM.! i of
                  Neg -> LFalse
                  Pos -> LTrue
                  _ -> x
                x -> x

        ixMap' <- blift $ unsafeNewArray_ @(STArray s) bnds
        for_ [ibeg .. iend] $ \i -> do
          t <- blift $ for (arr' `unsafeAt` i) $ unsafeRead ixMap'
          alg (fst $ gs3 `unsafeAt` i) t >>= blift . unsafeWrite ixMap' i

        blift $ unsafeFreeze ixMap'

      (tListSize, tList) <- HCons.consResult <$> readSTRef hcref
      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, listArray (0, tListSize - 1) tList)

    gs' = eixMappedGs2 arr ixMap gs
    gs'' = gs' <&> \case Zero -> (Zero, NoRefSign); x -> (x, Pos)
    bnds@(ibeg, iend) = bounds arr

    alg Zero _ = return $ error "accessing element without parents"
    alg count t = case share descend fst t of
      Left b -> return $ Left b
      Right x -> fmap Right $
        flip iterM x $ \t -> do
          t' <- sequence t
          i <- HCons.cons @"cons" (fmap fst t')
          return (i, Fix $ Compose $ Compose (count, t'))
      where
        descend (_, Fix (Compose (Compose gt))) = gt

{-# INLINEABLE simplifyDagUntilFixpoint #-}
simplifyDagUntilFixpoint ::
  forall p.
  (Eq p, Hashable p) =>
  Array Int Any ->
  (Array Int (Either Bool Int), Array Int (Term p Int)) ->
  (Array Int (Either Bool Int), Array Int (Term p Int))
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
