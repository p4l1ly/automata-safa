{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Ops.QMinCut where

import Control.Monad.Trans
import Data.Maybe
import Control.Lens
import Control.Monad.ST
import Data.List
import Data.Array
import Control.RecursionSchemes.Lens

import Afa
import Afa.Term.Mix
import Afa.Lib.QMinCut
import Afa.Lib
import Afa.Lib.LiftArray

qminCut :: forall p. AfaUnswallowed p -> AfaUnswallowed p
qminCut (Afa terms states init) = Afa terms' states'' init''
  where
  sinks = map fst$ ($ assocs terms)$ filter$ \(_, x) -> case x of
    Predicate _ -> True
    State _ -> True
    LTrue -> True
    _ -> False

  sources = map head$ group$ sort$ elems states

  states' = minCut terms sinks sources
  (init'', states'') = case terms'!init' of
    State q -> (q, listArray' states')
    _ -> let qs = listArray'$ init' : states' in (snd$ bounds qs, qs)

  (init', listArray' -> terms') = runST topToBottom

  topToBottom :: forall s. ST s (Int, [Term p Int Int])
  topToBottom = runNoConsT$ do
    (ixMap, listArray' -> below) <- runNoConsT$ partitionByCut terms states'
    ($ below)$ cataScanT' @(LSTArray s) traversed$ \case
      State q -> return$ fromJust$ snd$ ixMap!(states!q)
      x -> nocons x
    return$ fromJust$ snd$ ixMap!(states!init)

partitionByCut :: forall s p.
     Array Int (Term p Int Int)
  -> [Int]
  -> NoConsT (Term p Int Int) (NoConsT (Term p Int Int) (ST s))
       (Array Int (Int, Maybe Int))
partitionByCut nodes cut = ($ cutFlaggedNodes)$
  cataScanT' @(LLSTArray s) (_2 . traversed)$ \(cut, x) -> do
    belowIx <- nocons (fmap fst x)
    (belowIx,) <$> case cut of
      Just q -> fmap Just$ lift$ nocons$ State q
      _ | null x || any (isNothing . snd) x -> return Nothing
        | otherwise -> fmap Just$ lift$ nocons$ fmap (fromJust . snd) x
  where
  tagCut (Nothing, x) q = (Just q, x)
  cutFlaggedNodes = accum tagCut (fmap (Nothing,) nodes)$ zip cut [0..]
