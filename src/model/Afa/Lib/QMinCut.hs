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


maxFlow :: Foldable f
  => Array Int (f Int)
  -> [Int]
  -> Array Int Bool
  -> Array Int Bool
  -> Array Int (Maybe (Maybe Int))
maxFlow nodes sources sourceFlags sinkFlags = runST action
  where
  action :: forall s. ST s (Array Int (Maybe (Maybe Int)))
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
    unsafeFreeze residualGraphM

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


minCut :: Traversable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut nodes sources sinks = runST action where
  action :: forall s. ST s [Int]
  action = do
    let marks = isJust <$> maxFlow nodes sources sourceFlags sinkFlags
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

data Path2
  = Unvisited2
  | Visited2
  deriving (Eq, Show)

instance Semigroup Path2 where
  Visited2 <> _ = Visited2
  _ <> x = x

minCut2Lowest :: forall f. Traversable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut2Lowest nodes sources sinks =
  [ revIx i
  | (i, Visited2) <- assocs reachablePart
  , revSinkFlags!i || any (\j -> reachablePart!j == Unvisited2) (revNodes!i)
  ]
  where
  bnds = bounds nodes
  maxIx = snd bnds
  revIx = (maxIx -)
  revNodes = ixmap bnds revIx$ runST action where
    action :: forall s. ST s (Array Int [Int])
    action = do
      preds :: STArray s Int [Int] <- newArray bnds []
      for_ (assocs nodes)$ \(i, node) ->
        for_ node$ \j -> readArray preds j >>= writeArray preds j . (revIx i :)
      unsafeFreeze preds
  revSources = map revIx sinks
  revSinks = map revIx sources
  residualGraph = maxFlow revNodes revSources revSourceFlags revSinkFlags

  revSinkFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) revSinks
  revSourceFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) revSources

  reachablePart = runST action where
    action :: forall s. ST s (Array Int Path2)
    action = do
      arr <- newArray @(STArray s) (bounds nodes) Unvisited2
      for_ revSources$
        flip dfs arr$ \rec -> let rec' = rec . (Unvisited2,) in \case
          (Unvisited2, i) -> do
            writeArray arr i Visited2
            case residualGraph!i of
              Just (Just back) -> for_ (revNodes!back) rec' >> rec' back
              Just _ -> return ()
              _ -> for_ (revNodes!i) rec'
          (_, i) -> return ()
      unsafeFreeze arr

minCut2Highest :: forall f. Traversable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut2Highest nodes sources sinks =
  [ i
  | (i, Visited2) <- assocs reachablePart
  , sinkFlags!i || any (\j -> reachablePart!j == Unvisited2) (nodes!i)
  ]
  where
  bnds = bounds nodes
  residualGraph = maxFlow nodes sources sourceFlags sinkFlags

  sinkFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sinks
  sourceFlags = accumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sources

  reachablePart = runST action where
    action :: forall s. ST s (Array Int Path2)
    action = do
      arr <- newArray @(STArray s) (bounds nodes) Unvisited2
      for_ sources$
        flip dfs arr$ \rec -> let rec' = rec . (Unvisited2,) in \case
          (Unvisited2, i) -> do
            writeArray arr i Visited2
            case residualGraph!i of
              Just (Just back) -> for_ (nodes!back) rec' >> rec' back
              Just _ -> return ()
              _ -> for_ (nodes!i) rec'
          (_, i) -> return ()
      unsafeFreeze arr
