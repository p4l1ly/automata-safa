{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Afa.Lib.QMinCut where

import Data.List
import Data.Maybe
import Control.Monad
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


maxFlow :: Foldable f => Array Int (f Int) -> [Int] -> [Int] -> Array Int Bool
maxFlow nodes sources sinks = runST action
  where
  action :: forall s. ST s (Array Int Bool)
  action = do
    residualGraphM <- newArray @(STArray s) (bounds nodes) Nothing
    let getPath = do
          arr <- newArray @(STArray s) (bounds nodes) Unvisited
          for_ sources$ \src -> writeArray arr src$ Visited$ Endo id
          runExceptT$ for_ sources$
            dfs (traversal residualGraphM arr)$ LiftArray arr
        subtractPath ixs = do
          writeArray residualGraphM (head ixs)$ Just Nothing
          for_ (zip (tail ixs) ixs)$ \(next, this) ->
            if next < this
            then writeArray residualGraphM next (Just$ Just this)
            else do
              old <- readArray residualGraphM this
              when (old == Just (Just next))$
                writeArray residualGraphM this Nothing
        rec = getPath >>= \case Left p -> subtractPath p >> rec; _ -> return ()
    rec
    fmap isJust <$> unsafeFreeze residualGraphM

  traversal residualGraphM arr rec = \case
    (Visited pp, i) -> do
      lift$ writeArray arr i Blind
      lift (readArray residualGraphM i) >>= \case
        Just (Just back) -> for_ (nodes!back) (recBackDown back) >> rec' back
        Just _ -> return ()
        _ | sinkFlags!i -> throwE$ pp `appEndo` [i]
          | otherwise -> for_ (nodes!i) recDown
      where
      rec' = rec . (Visited$ pp <> Endo (i:),)
      recDown j = unless (sourceFlags!j)$ rec' j
      recBackDown back j = unless (sourceFlags!j)$ rec'' j
        where rec'' = rec . (Visited$ pp <> Endo (\xs -> i:back:xs),)
    _ -> return ()

  sinkFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sinks
  sourceFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sources


minCut :: Traversable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut nodes sources sinks = runST action where
  action :: forall s. ST s [Int]
  action = do
    let marks = maxFlow nodes sources sinks
    let marks1 = ixedNodes & cataScan (_2 . traversed) %~ \(i, fb) ->
          marks!i || or fb && not (sinkFlags!i)

    let setter rec = \(g, i) -> let overmined = marks!i || getAny g in
          overmined <$ for_ (nodes!i) (rec . (Any overmined,))
    marks2Init :: STArray s Int Any <- newArray (bounds nodes) (Any False)
    marks2M :: STArray s Int Bool <- marks2Init & anaScanT2 setter return
    marks2 <- unsafeFreeze marks2M

    if all (marks1!) sinks  -- topmost min cut: all (marks2!) sources
      then return sinks  -- topmost min cut: return sources
      else do
        let newSources = map head$ group$ sort
              [ j
              | (i, node) <- elems ixedNodes
              , area!i && not (marks2!i)
              , j <- toList node
              , marks2!j && not (sourceFlags!j)
              ]
        let newSinks = map head$ group$ sort
              [ i
              | (i, node) <- elems ixedNodes
              , marks1!i && not (sinkFlags!i)
              , any (\j -> area!j && not (marks1!j)) node
              ]
        let sources' = filter (marks2!) sources ++ newSources
        let sinks' = filter (marks1!) sinks ++ newSinks
        return$ minCut nodes sources' sinks'

  ixedNodes = listArray (bounds nodes)$ zip [0..] (elems nodes)

  sinkFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sinks
  sourceFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sources

  aboveSinks = ixedNodes & cataScan (_2 . traversed) %~ \(i, fb) -> sinkFlags!i || or fb
  underSources = runST action where
    action :: forall s. ST s (Array Int Bool)
    action = do
      let setter rec = \(g, i) -> let overmined = sourceFlags!i || getAny g in
            overmined <$ for_ (nodes!i) (rec . (Any overmined,))
      marks2Init :: STArray s Int Any <- newArray (bounds nodes) (Any False)
      marks2M :: STArray s Int Bool <- marks2Init & anaScanT2 setter return
      unsafeFreeze marks2M

  area = listArray (bounds nodes)$ zipWith (&&) (elems aboveSinks) (elems underSources)
