{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Afa (
  Afa (..),
  MixTermIFree,
  AfaSwallowed,
  AfaUnswallowed,
  delayPredicates,
  reorderStates,
  simplifyAll,
  simplifyStatesAndMixTs,
) where

import Debug.Trace

import Afa.Lib (DumbCount (..), listArray')
import Afa.Lib.LiftArray
import Afa.Term.Mix (ChildMod (..), Term (..), modChilds, pureChildMod)
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Mix.Simplify as MTerm
import Control.Arrow
import Control.Lens
import Control.Monad
import Control.Monad.Free
import Control.Monad.ST
import Control.Monad.Trans
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.HashCons
import Control.RecursionSchemes.Utils.NoCons
import Data.Array
import Data.Array.Base (unsafeAccumArray, unsafeAt, unsafeWrite)
import Data.Array.ST
import Data.Array.Unsafe
import Data.Either
import Data.Fix
import Data.Foldable
import Data.Functor.Compose
import Data.Hashable
import Data.List (partition)
import Data.Maybe
import Data.Monoid (Any (..), Endo (..))
import Data.Traversable
import GHC.Exts (groupWith, sortWith)

data Afa terms states init = Afa
  { terms :: !terms
  , states :: !states
  , initState :: !init
  }
  deriving (Show, Eq)

type MixTermIFree p = Free (Term p Int) Int
type AfaSwallowed p = Afa (Array Int (MixTermIFree p)) (Array Int (MixTermIFree p)) Int
type AfaUnswallowed p = Afa (Array Int (Term p Int Int)) (Array Int Int) Int

{-# INLINEABLE delayPredicates #-}
delayPredicates :: (Show p) => AfaUnswallowed p -> AfaUnswallowed p
delayPredicates afa@Afa{terms, states} =
  afa
    { terms = listArray' $ elems terms1 ++ terms2
    , states = listArray' $ elems states ++ states2
    }
  where
    stateCount = rangeSize (bounds states)
    termCount = rangeSize (bounds terms)
    Identity ((terms1, terms2), states2) =
      runNoConsTFrom stateCount $
        runNoConsTFrom termCount $
          for terms $ \case
            p@(Predicate _) -> (nocons p >>= lift . nocons) <&> State
            x -> return x

{-# INLINEABLE reorderStates #-}
reorderStates ::
  Functor f =>
  Afa (f (Term p' Int t')) (Array Int a) Int ->
  Afa (f (Term p' Int t')) (Array Int a) Int
reorderStates afa@Afa{initState = 0} = afa
reorderStates Afa{terms, states, initState} =
  Afa
    { initState = 0
    , states = states // [(0, states ! initState), (initState, states `unsafeAt` 0)]
    , terms =
        terms
          <&> MTerm.appMTFun
            MTerm.mtfun0
              { MTerm.mtfunQ = \case
                  0 -> initState
                  q
                    | q == initState -> 0
                    | otherwise -> q
              }
    }

{-# INLINEABLE simplifyAll #-}
simplifyAll :: (Eq p, Hashable p, Show p) => AfaUnswallowed p -> Either Bool (AfaUnswallowed p)
simplifyAll (Afa terms states initState) = do
  (terms', states', initState') <-
    simplifyStatesAndMixTs ixMap terms states initState
  return $ Afa terms' states' initState'
  where
    ixMap = listArray (bounds terms) $ map Right [0 ..]

data ReachableMark = Unvisited | Recur | Visited
instance Semigroup ReachableMark where
  Unvisited <> x = x
  x <> _ = x

{-# INLINEABLE markReachable #-}
markReachable ::
  Foldable f =>
  Afa (Array Int (Term p Int Int)) (Array Int (f Int)) Int ->
  Array Int Bool
markReachable (Afa terms states init) =
  unsafeAccumArray (\_ _ -> True) False (bounds states) $
    (init, ()) :
      [ (q, ())
      | (i@(unsafeAt terms -> State q), True) <- zip [0 ..] (elems termMarks)
      ]
  where
    termMarks = runST getMarks <&> \case Unvisited -> False; _ -> True

    getMarks :: forall s. ST s (Array Int ReachableMark)
    getMarks = do
      marks <- newArray @(STArray s) (bounds terms) Unvisited
      for_ (states `unsafeAt` init) $ \i -> do
        unsafeWrite marks i Recur
        dfs (traversal marks) marks i
      unsafeFreeze marks

    traversal arr rec (x, i) = case x of
      Recur -> do
        unsafeWrite arr i Visited
        void $
          terms `unsafeAt` i
            & modChilds
              pureChildMod
                { lQ = \q -> for_ (states `unsafeAt` q) $ \i -> rec (Recur, i)
                , lT = \j -> rec (Recur, j)
                }
      Visited -> return ()
      Unvisited -> error "visiting unvisited"

{-# INLINEABLE simplifyStatesAndMixTs #-}
simplifyStatesAndMixTs ::
  forall p.
  (Eq p, Hashable p, Show p) =>
  Array Int (Either Bool Int) ->
  Array Int (MTerm.Term p Int Int) ->
  Array Int Int ->
  Int ->
  Either Bool (Array Int (MTerm.Term p Int Int), Array Int Int, Int)
simplifyStatesAndMixTs ixMap mterms states init = case sequence states1 of
  Right states' | cost mterms <= cost mterms3 -> Right (mterms3, states2, init2)
  _ -> states1 `unsafeAt` init >> simplifyStatesAndMixTs ixMap3 mterms3 states2 init2
  where
    cost ts = (rangeSize $ bounds ts, sum $ fmap length ts)
    states1 = fmap (ixMap `unsafeAt`) states

    parented = markReachable $ Afa mterms states1 init
    (lefts, rights) =
      partition (isLeft . snd) $
        zipWith noparentLeft [0 ..] (elems states1)
      where
        noparentLeft i x = if parented `unsafeAt` i then (i, x) else (i, Left False)

    lefts' = lefts <&> \case (i, Left x) -> (i, x)
    rights' = rights <&> \case (i, Right x) -> (i, x)

    groups = groupWith snd $ sortWith snd rights' -- PERF: use hashmap? radix grouping?
    states2 = listArray' $ snd . head <$> groups
    oldToNew = concat $ zipWith (\i' xs -> map ((,i') . fst) xs) [0 ..] groups

    qMap :: Array Int (Either Bool Int)
    qMap = array (bounds states) $ map (second Left) lefts' ++ map (second Right) oldToNew

    init2 = qMap `unsafeAt` init & \case Right x -> x

    (ixMap2, listArray' -> mterms2) = runST action
      where
        action :: forall s. ST s (Array Int (Either Bool Int), [MTerm.Term p Int Int])
        action =
          runHashConsT $
            fmap (fmap fst) <$> cataScanT' @(LSTArray s) traversed alg mterms

    mgs = unsafeAccumArray (\_ x -> x) mempty (bounds mterms) $ map (,Any True) (elems states2)
    (ixMap3, mterms3) = MTerm.simplifyDagUntilFixpoint mgs (ixMap2, mterms2)

    alg t = case MTerm.modChilds MTerm.pureChildMod{MTerm.lQ = (qMap `unsafeAt`)} t of
      Left b -> return $ Left b
      Right t -> case MTerm.simplify ((Many,) . getCompose . unFix . snd) fst t of
        Left b -> return $ Left b
        Right (Left it) -> return $ Right it
        Right (Right t) -> Right . (,Fix $ Compose t) <$> hashCons' (fmap fst t)
