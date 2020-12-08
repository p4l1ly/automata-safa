{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NamedFieldPuns #-}

module Afa.Convert.Separated where

import Data.Bifunctor
import Control.Monad.ST
import Data.Array
import Data.Array.Unsafe
import Data.Array.ST
import Afa
import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import Control.RecursionSchemes.Lens
import Control.Monad
import Data.Maybe
import Control.Lens
import Afa.Term.Mix
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

separateAfa :: AfaUnswallowed p -> AfaUnswallowed p
separateAfa afa@Afa{terms, states} =
  afa{ terms = terms', states = (ixMap!) <$> states }
  where (ixMap, terms') = separateTerms terms

separateTerms :: forall p q.
  Array Int (Term p q Int) -> (Array Int Int, Array Int (Term p q Int))
separateTerms arr = second listArray'$ runST action where
  action :: forall s. ST s (Array Int Int, [Term p q Int])
  action = runNoConsT$ fmap (fmap fst)$
    cataScanT @(LiftArray (STArray s)) traversed separate arr >>= unsafeFreeze

separate
  :: Monad m
  => Term p q (Int, SepData Int)
  -> NoConsT (Term p q Int) m (Int, SepData Int)
separate (Predicate p) = (, PureP) <$> nocons (Predicate p)
separate (State q) = (, PureQ) <$> nocons (State q)
separate (Or tseps) = do
  result <- nocons$ Or$ NE.map fst tseps
  case partitionBySepData$ NE.toList tseps of
    (_, [], [], []) -> return (result, PureP)
    ([], _, [], []) -> return (result, PureQ)
    (purePs, pureQs, mAnds, mOrs) -> do
      pureP <- nothingSingleMulti Or$ purePs ++ mapMaybe (^._2) mOrs
      pureQ <- nothingSingleMulti Or$ pureQs ++ mapMaybe (^._3) mOrs
      return (result, MixedOr pureP pureQ mAnds)
separate (And tseps) = case partitionBySepData$ NE.toList tseps of
  (purePs, [], [], []) -> (, PureP) <$> nocons (And$ NE.fromList purePs)
  ([], pureQs, [], []) -> (, PureQ) <$> nocons (And$ NE.fromList pureQs)
  (purePs, pureQs, mAnds, []) -> do
    pureP <- nothingSingleMulti And$ purePs ++ map (^._2) mAnds
    pureQ <- nothingSingleMulti And$ pureQs ++ map (^._3) mAnds
    (, MixedAnd (fromJust pureP) (fromJust pureQ)) <$> nocons (And$ NE.map fst tseps)
  (purePs, pureQs, mAnds, mOrs) -> do
    let
      mAnds' = mAnds <&> \(t, tP, tQ) -> (t, MixedAnd tP tQ)
      purePs' = purePs <&> (, PureP)
      pureQs' = pureQs <&> (, PureQ)

      mOrs' = flip map mOrs$ \(_, tP, tQ, mts) -> catMaybes
        $ (tP <&> (, PureP))
        : (tQ <&> (, PureQ))
        : map (\(t, tP, tQ) -> Just (t, MixedAnd tP tQ)) mts

      step xs1 xs2 = sequence$ do
        x1 <- xs1
        x2 <- xs2
        return$ separate$ And (x1 :| [x2])

    starter <- case purePs' ++ pureQs' ++ mAnds' of
      [] -> return []
      [x] -> return [[x]]
      x:xs -> separate (And$ x:|xs) <&> \x -> [[x]]

    let action0:actions = starter ++ mOrs'
    x <- foldM step action0 actions
    separate$ Or$ NE.fromList x
separate LTrue = (, PureQ) <$> nocons LTrue

data SepData t
  = PureP
  | PureQ
  | MixedAnd t t
  | MixedOr (Maybe t) (Maybe t) [(t, t, t)]
  deriving Functor

partitionBySepData
  :: [(a, SepData t)]
  -> ([a], [a], [(a, t, t)], [(a, Maybe t, Maybe t, [(t, t, t)])])
partitionBySepData = foldr step ([], [], [], []) where
  step (a, PureP) = _1 %~ (a:)
  step (a, PureQ) = _2 %~ (a:)
  step (a, MixedAnd tP tQ) = _3 %~ ((a, tP, tQ):)
  step (a, MixedOr tP tQ mts) = _4 %~ ((a, tP, tQ, mts):)

nothingSingleMulti
  :: Monad m => (NonEmpty Int -> f Int) -> [Int] -> NoConsT (f Int) m (Maybe Int)
nothingSingleMulti f = \case
  [x] -> return$ Just x
  xs -> traverse (nocons . f)$ NE.nonEmpty xs
