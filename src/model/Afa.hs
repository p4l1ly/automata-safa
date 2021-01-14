{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Afa
  (Afa(..)
  , MixTermIFree
  , AfaSwallowed
  , AfaUnswallowed
  , delayPredicates
  , reorderStates
  , simplifyAll
  , simplifyStatesAndMixTs
  ) where

import Debug.Trace

import Control.Monad.Free
import Data.Foldable
import Data.Maybe
import Control.Monad
import Data.Array.ST
import Data.Array.Unsafe
import Control.Lens
import GHC.Exts (sortWith, groupWith)
import Data.List (partition)
import Data.Either
import Control.Arrow
import Data.Fix
import Data.Functor.Compose
import Data.Monoid (Endo(..), Any(..))
import Control.Monad.ST
import Data.Array
import Afa.Term.Mix (Term(..), modChilds, pureChildMod, ChildMod(..))
import qualified Afa.Term.Mix as MTerm
import Control.RecursionSchemes.Lens
import Control.Monad.Trans
import Data.Traversable
import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import Data.Hashable
import qualified Afa.Term.Mix.Simplify as MTerm

data Afa terms states init = Afa
  { terms :: terms
  , states :: states
  , initState :: init
  }
  deriving (Show, Eq)

type MixTermIFree p = Free (Term p Int) Int
type AfaSwallowed p = Afa (Array Int (MixTermIFree p)) (Array Int (MixTermIFree p)) Int
type AfaUnswallowed p = Afa (Array Int (Term p Int Int)) (Array Int Int) Int


delayPredicates :: (Show p) => AfaUnswallowed p -> AfaUnswallowed p
delayPredicates afa@Afa{terms, states} = afa
  { terms = listArray'$ elems terms1 ++ terms2
  , states = listArray'$ elems states ++ states2
  }
  where
  stateCount = rangeSize (bounds states)
  termCount = rangeSize (bounds terms)
  Identity ((terms1, terms2), states2) =
    runNoConsTFrom stateCount$ runNoConsTFrom termCount$
      for terms$ \case
        p@(Predicate _) -> (nocons p >>= lift . nocons) <&> State
        x -> return x


reorderStates :: Functor f
  => Afa (f (Term p' Int t')) (Array Int a) Int
  -> Afa (f (Term p' Int t')) (Array Int a) Int
reorderStates afa@Afa{initState = 0} = afa
reorderStates Afa{terms, states, initState} = Afa
  { initState = 0
  , states = states // [(0, states!initState), (initState, states!0)]
  , terms = terms <&> runIdentity . MTerm.modChilds MTerm.pureChildMod
      { MTerm.lQ = Identity . \case
          0 -> initState
          q | q == initState -> 0
            | otherwise -> q
      }
  }


simplifyAll :: (Eq p, Hashable p, Show p) => AfaUnswallowed p -> Either Bool (AfaUnswallowed p)
simplifyAll (Afa terms states initState) = do
  (terms', states', initState') <-
    simplifyStatesAndMixTs ixMap terms states initState
  return$ Afa terms' states' initState'
  where ixMap = listArray (bounds terms)$ map Right [0..]


data ReachableMark = Unvisited | Recur | Visited
instance Semigroup ReachableMark where
  Unvisited <> x = x
  x <> _ = x

markReachable :: Foldable f => Afa (Array Int (Term p Int Int)) (Array Int (f Int)) Int
  -> Array Int Bool
markReachable (Afa terms states init) =
  accumArray (\_ _ -> True) False (bounds states)$ (init, ()) :
    [ (q, ())
    | (i@((terms!) -> State q), True)<- zip [0..] (elems termMarks)
    ]
  where
  termMarks = runST getMarks <&> \case Unvisited -> False; _ -> True

  getMarks :: forall s. ST s (Array Int ReachableMark)
  getMarks = do
    marks <- newArray @(STArray s) (bounds terms) Unvisited
    for_ (states!init)$ \i -> do
      writeArray marks i Recur
      dfs (traversal marks) marks i
    unsafeFreeze marks

  traversal arr rec (x, i) = case x of
    Recur -> do
      writeArray arr i Visited
      void$ terms!i & modChilds pureChildMod
        { lQ = \q -> for_ (states!q)$ \i -> rec (Recur, i)
        , lT = \j -> rec (Recur, j)
        }
    Visited -> return ()
    Unvisited -> error "visiting unvisited"


simplifyStatesAndMixTs :: forall p. (Eq p, Hashable p, Show p)
  => Array Int (Either Bool Int)
  -> Array Int (MTerm.Term p Int Int)
  -> Array Int Int
  -> Int
  -> Either Bool (Array Int (MTerm.Term p Int Int), Array Int Int, Int)
simplifyStatesAndMixTs ixMap mterms states init = case sequence states1 of
  Right states' | cost mterms <= cost mterms3 -> Right (mterms3, states2, init2)
  _ -> states1!init >> simplifyStatesAndMixTs ixMap3 mterms3 states2 init2
  where
  cost ts = (rangeSize$ bounds ts, sum$ fmap length ts)
  states1 = fmap (ixMap!) states

  parented = markReachable$ Afa mterms states1 init
  (lefts, rights) = partition (isLeft . snd)$
    zipWith noparentLeft [0..] (elems states1)
    where noparentLeft i x = if parented!i then (i, x) else (i, Left False)

  lefts' = lefts <&> \case (i, Left x) -> (i, x)
  rights' = rights <&> \case (i, Right x) -> (i, x)

  groups = groupWith snd$ sortWith snd rights'  -- PERF: use hashmap? radix grouping?
  states2 = listArray'$ snd . head <$> groups
  oldToNew = concat$ zipWith (\i' xs -> map ((, i') . fst) xs) [0..] groups

  qMap :: Array Int (Either Bool Int)
  qMap = array (bounds states)$ map (second Left) lefts' ++ map (second Right) oldToNew

  init2 = qMap!init & \case Right x -> x

  (ixMap2, listArray' -> mterms2) = runST action where
    action :: forall s. ST s (Array Int (Either Bool Int), [MTerm.Term p Int Int])
    action = runHashConsT$
      fmap (fmap fst) <$> cataScanT' @(LSTArray s) traversed alg mterms

  mgs = accumArray (\_ x -> x) mempty (bounds mterms)$ map (, Any True) (elems states2)
  (ixMap3, mterms3) = MTerm.simplifyDagUntilFixpoint mgs (ixMap2, mterms2)

  alg t = case MTerm.modChilds MTerm.pureChildMod{ MTerm.lQ = (qMap!) } t of
    Left b -> return$ Left b
    Right t -> case MTerm.simplify (getCompose . unFix . snd) fst t of
      Left b -> return$ Left b
      Right (Left it) -> return$ Right it
      Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)
