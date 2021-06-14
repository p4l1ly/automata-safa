{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Ops.QMinCut where

import Data.Array.Base (unsafeAt)
import Control.Monad.Trans
import Data.Maybe
import Control.Lens
import Control.Monad.ST
import Data.List
import Data.Array
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons

import Afa
import Afa.Term.Mix
import Afa.Lib.QMinCut
import Afa.Lib
import Afa.Lib.LiftArray

{-# INLINABLE qminCut #-}
qminCut :: forall p. AfaUnswallowed p -> AfaUnswallowed p
qminCut (Afa terms states init) = Afa terms' states''' init''
  where
  initTerm = states!init
  sinks = map fst$ ($ assocs terms)$ filter$ \(i, x) -> case x of
    Predicate _ -> True
    State _ -> True
    LTrue -> True
    _ -> i == initTerm
  sources = map head$ group$ sort$ elems states
  states' = minCut2Lowest terms sources sinks

  ((init', states''), listArray' -> terms') = runST topToBottom
  (init'', states''') = case terms' `unsafeAt` init' of
    State q -> (q, listArray' states'')
    _ -> error "init did not remain" -- let qs = listArray'$ states'' ++ [init'] in (snd$ bounds qs, qs)

  topToBottom :: forall s. ST s ((Int, [Int]), [Term p Int Int])
  topToBottom = runNoConsT$ do
    (ixMap, listArray' -> below) <- runNoConsT$ partitionByCut terms states'
    ixMapNewTop <- ($ below)$ cataScanT' @(LSTArray s) traversed$ \case
      State q -> return$ fromJust$ snd$ ixMap `unsafeAt` (states `unsafeAt` q)
      x -> nocons x
    return
      ( fromJust$ snd$ ixMap `unsafeAt` (states `unsafeAt` init)
      , map (ixMapNewTop `unsafeAt`) states'
      )

{-# INLINABLE partitionByCut #-}
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
