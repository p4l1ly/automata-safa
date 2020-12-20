{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Ops.QMinCut where

import Debug.Trace

import Control.Monad.Trans
import Control.Monad.Trans.Except
import Data.Monoid (Any(..), Endo(..))
import Control.Lens
import Data.Array.Unsafe
import Data.Foldable
import Control.Monad.ST
import Data.Array
import Data.Array.ST
import Control.RecursionSchemes.Lens

import Afa.Lib.LiftArray

data Dfs = Unreachable | Recur | Reachable deriving Show
instance Semigroup Dfs where
  Unreachable <> x = x
  _ <> _ = Reachable

trueIndices :: [Bool] -> [Int]
trueIndices xs = [i | (i, True) <- zip [0..] xs]

isReachable Unreachable = False
isReachable _ = True

data Path
  = Unvisited
  | Visited (Endo [Int])
  | Blind

showInPath Unvisited = "U"
showInPath (Visited pp) = "V" ++ show (pp `appEndo` [])
showInPath Blind = "B"

instance Semigroup Path where
  Blind <> _ = Blind
  Visited _ <> _ = Blind
  _ <> x = x

paths :: Foldable f => Array Int (f Int) -> [Int] -> Array Int Bool
paths nodes sources = runST action
  where
  action :: forall s. ST s (Array Int Bool)
  action = do
    blockersM <- newArray @(STArray s) (bounds nodes) False
    let getPath = do
          blockers <- unsafeFreeze blockersM
          arr <- newArray @(STArray s) (bounds nodes) Unvisited
          for_ sources$ \src -> writeArray arr src$ Visited$ Endo id
          runExceptT$ for_ sources$
            dfs (traversal blockers arr)$ LiftArray arr
        subtractPath ixs = for_ ixs$ \ix -> writeArray blockersM ix True
        rec = getPath >>= \case Left p -> subtractPath p >> rec; _ -> return ()
    rec
    unsafeFreeze blockersM

  traversal blockers arr rec = \case
    (Visited pp, i)
      | blockers!i -> return ()
      | null node -> throwE$ pp `appEndo` [i]
      | otherwise -> do
          lift$ writeArray arr i Blind
          for_ node$ rec . (Visited$ pp <> Endo (i:),)
      where node = nodes!i
    _ -> return ()

minCut :: Traversable f => Array Int (f Int) -> [Int] -> [Int]
minCut nodes sources = runST action where
  action :: forall s. ST s [Int]
  action = do
    let (traceShowId -> marks) = paths nodes sources
    let (traceShowId -> marks10) = ixedNodes & cataScan (_2 . traversed) %~ \(i, fb) ->
          let undermined = all snd fb && not (null fb)
              mark = marks!i
          in (not undermined, mark || undermined)
    let marks1 = fmap fst marks10
    let setter rec = \case
          (Any False, _) -> pure False
          (Any True, i) -> if marks1!i
            then pure True
            else True <$ for_ (nodes!i) (rec . (Any True,))

    marks2Init :: STArray s Int Any <- unsafeThaw$
      accumArray (\_ _ -> Any True) (Any False) (bounds nodes)$ map (, ()) sources
    marks2M :: STArray s Int Bool <- marks2Init & anaScanT2 setter return
    trueIndices . elems <$> unsafeFreeze marks2M

  ixedNodes = listArray (bounds nodes)$ zip [0..] (elems nodes)
