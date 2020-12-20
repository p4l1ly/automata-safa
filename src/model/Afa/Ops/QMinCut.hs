{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}

module Afa.Ops.QMinCut where

import Control.Monad
import Control.Monad.Trans
import Data.Bifunctor
import Data.Array.Unsafe
import Data.Foldable
import Control.Monad.Trans.Except
import Control.Monad.ST
import Data.Array
import Data.Array.ST
import Control.RecursionSchemes.Lens
import Data.Monoid

import Afa.Lib.LiftArray

data Position = Source | Sink | Middle

data InPath
  = Unvisited
  | Visited (Endo [Int])
  | Blind

showInPath Unvisited = "U"
showInPath (Visited pp) = "V" ++ show (pp `appEndo` [])
showInPath Blind = "B"

instance Semigroup InPath where
  Blind <> _ = Blind
  Visited _ <> _ = Blind
  _ <> x = x

maxFlow :: Array Int (Maybe ([Int], [Int])) -> [Int] -> Array Int Bool
maxFlow nodes sources = runST action 
  where
  action :: forall s. ST s (Array Int Bool)
  action = do
    blockersM <- newArray @(STArray s) (bounds nodes) False
    let getPath = do
          blockers <- unsafeFreeze blockersM
          passArr <- newArray @(STArray s) (bounds nodes) (Unvisited, Unvisited)
          for_ sources$ \src -> writeArray passArr src (Visited$ Endo id, Unvisited)
          runExceptT$ for_ sources$ dfs (traversal blockers passArr)$ LiftArray passArr
        subtractPath ixs = for_ ixs$ \ix -> writeArray blockersM ix True
        rec = getPath >>= \case Left p -> subtractPath p >> rec; _ -> return ()
    rec
    unsafeFreeze blockersM

  traversal blockers passArr rec (v, i) = do
    lift$ writeArray passArr i$ bimap visitedToBlind visitedToBlind v
    traversal1 snd snd first fst True
    void$ traversal1 fst fst second snd False
    where
    traversal1 getMine getMine2 modOther getOther downwards = case getMine v of
      Blind -> return ()
      Visited pp -> add pp
      Unvisited
        | blockers!i && downwards -> return ()
        | otherwise -> add$ case getOther v of
            Visited pp -> if blockers!i then pp else pp <> Endo (i:)
      where
      add pp = do
        case nodes!i of
          Nothing -> throwE$ pp `appEndo` []
          Just (getMine2 -> neighbours) -> for_ neighbours (rec . (childG,))
        where childG = modOther (const$ Visited pp) (Unvisited, Unvisited)

    visitedToBlind (Visited _) = Blind
    visitedToBlind x = if blockers!i then x else Blind

trueIndices :: [Bool] -> [Int]
trueIndices xs = [i | (i, True) <- zip [0..] xs]

data Reachable = Unreachable | Recur | Reachable deriving Show
instance Semigroup Reachable where
  Unreachable <> x = x
  _ <> _ = Reachable

isReachable Unreachable = False
isReachable _ = True

minCut :: Array Int (Maybe ([Int], [Int])) -> [Int] -> [Int]
minCut nodes sources = runST action where
  action :: forall s. ST s [Int]
  action = do
    reachableM <- newArray @(STArray s) (bounds nodes) (Unreachable, Unreachable)
    for_ sources$ \src -> writeArray reachableM src (Recur, Unreachable)
    for_ sources$ dfs (traversal reachableM) reachableM
    reachable <- unsafeFreeze reachableM
    let isBorder (Reachable, Unreachable) = True
        isBorder _ = False
    return$ trueIndices$ map isBorder$ elems reachable

  blockers = maxFlow nodes sources
  traversal arr rec (x, i) = do
    writeArray arr i$ bimap recurToReachable recurToReachable x
    traversal1 snd snd first True
    void$ traversal1 fst fst second False
    where
    traversal1 getMine getMine2 modOther downwards = case getMine x of
      Reachable -> return ()
      Unreachable | blockers!i && downwards -> return ()
      _ -> add
      where
      add = case nodes!i of
        Nothing -> return ()
        Just (getMine2 -> neighbours) -> for_ neighbours (rec . (childG,))
        where childG = modOther (const Recur) (Unreachable, Unreachable)

    recurToReachable Unreachable | blockers!i = Unreachable
    recurToReachable _ = Reachable
