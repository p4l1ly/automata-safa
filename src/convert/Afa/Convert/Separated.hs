{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.Separated where

import Control.Arrow
import Control.Monad
import Data.Maybe
import Control.Monad.Free
import Control.Lens
import Afa.Term.Mix
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

data SepData t
  = PureP
  | PureQ
  | MixedAnd t t
  | MixedOr (Maybe t) (Maybe t) [(t, t, t)]
  deriving Functor

newtype TSepData t = TSepData (t, SepData t) deriving Functor

partitionBySepData
  :: [(a, SepData t)]
  -> ([a], [a], [(a, t, t)], [(a, Maybe t, Maybe t, [(t, t, t)])])
partitionBySepData = foldr step ([], [], [], []) where
  step (a, PureP) = _1 %~ (a:)
  step (a, PureQ) = _2 %~ (a:)
  step (a, MixedAnd t1 t2) = _3 %~ ((a, t1, t2):)
  step (a, MixedOr t1 t2 mts) = _4 %~ ((a, t1, t2, mts):)

nothingSingleMulti
  :: (NonEmpty (Free f t) -> f (Free f t)) -> [Free f t] -> Maybe (Free f t)
nothingSingleMulti f = \case
  [x] -> Just x
  xs -> Free . f <$> NE.nonEmpty xs

nothingSingleMulti'
  :: (NonEmpty (Free f t) -> f (Free f t)) -> [t] -> Maybe (Free f t)
nothingSingleMulti' f = nothingSingleMulti f . fmap Pure

separate :: Term p q (t, SepData t) -> (Free (Term p q) t, SepData (Free (Term p q) t))
separate (Predicate p) = (Free$ Predicate p, PureP)
separate (State q) = (Free$ State q, PureQ)
separate (Or tseps) = (Free$ Or$ NE.map (Pure . fst) tseps,)$ 
  case (null purePs, null pureQs, null mAnds, null mOrs) of
    (False, True, True, True) -> PureP
    (True, False, True, True) -> PureQ
    _ -> let
      pureP  = nothingSingleMulti' Or$ purePs ++ mapMaybe (^._2) mOrs
      pureQ  = nothingSingleMulti' Or$ pureQs ++ mapMaybe (^._3) mOrs
      mAnds' = map (\(t, tP, tQ) -> (Pure t, Pure tP, Pure tQ)) mAnds
      in MixedOr pureP pureQ mAnds'
  where
  (purePs, pureQs, mAnds, mOrs) = partitionBySepData$ NE.toList tseps
separate (And tseps) = case partitionBySepData$ NE.toList tseps of
  (purePs, [], [], []) -> (Free$ And$ NE.fromList$ map Pure purePs, PureP)
  ([], pureQs, [], []) -> (Free$ And$ NE.fromList$ map Pure pureQs, PureQ)
  (purePs, pureQs, mAnds, []) -> (Free$ And$ NE.map (Pure . fst) tseps,)$ let
    pureP = nothingSingleMulti' And$ purePs ++ map (^._2) mAnds
    pureQ = nothingSingleMulti' And$ pureQs ++ map (^._3) mAnds
    in MixedAnd (fromJust pureP) (fromJust pureQ)
  (purePs, pureQs, mAnds, mOrs) -> let
    mAnds' = mAnds <&> \(t, tP, tQ) -> (Pure t, MixedAnd (Pure tP) (Pure tQ))
    purePs' = purePs <&> \t -> (Pure t, PureP)
    pureQs' = pureQs <&> \t -> (Pure t, PureQ)

    starter = case purePs' ++ pureQs' ++ mAnds' of
      [] -> []
      [x] -> [[x]]
      x:xs -> [[join *** fmap join$ separate$ And$ x:|xs]]

    mOrs' = flip map mOrs$ \(_, tP, tQ, mts) -> catMaybes
      $ (tP <&> \t -> (Pure t, PureP))
      : (tQ <&> \t -> (Pure t, PureQ))
      : map (\(t, tP, tQ) -> Just (Pure t, MixedAnd (Pure tP) (Pure tQ))) mts

    (join -> ort, fmap join -> orsepd) = separate$ Or$ NE.fromList x

    x = foldl1 step$ starter ++ mOrs'
    step xs1 xs2 =
      [ join *** fmap join$ separate$ And (x1 :| [x2])
      | x1 <- xs1
      , x2 <- xs2
      ]
    in (ort, orsepd)
separate LTrue = (Free LTrue, PureQ)
