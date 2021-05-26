{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ForeignFunctionInterface #-}

module Afa.Lib.QMinCut where

import System.IO.Unsafe
import Foreign.Ptr
import Foreign.Storable
import Foreign.ForeignPtr
import Data.Word
import qualified Data.Array.CArray as CA
import Data.Traversable
import Data.Array.Base (unsafeRead, unsafeWrite, unsafeAccumArray, numElements, unsafeAt)
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
import Control.RecursionSchemes.Utils.NoCons

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


{-# INLINABLE maxFlow #-}
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
          for_ sources$ \src -> unsafeWrite arr src$ Visited$ Endo id
          runExceptT$ for_ sources$
            dfs (traversal residualGraphM arr)$ LiftArray arr
        subtractPath ixs = do
          unsafeWrite residualGraphM (head ixs)$ Just Nothing
          for_ (zip (tail ixs) ixs)$ \(next, this) ->
            if next < this
            then unsafeWrite residualGraphM next (Just$ Just this)
            else do
              old <- unsafeRead residualGraphM this
              when (old == Just (Just next))$
                unsafeWrite residualGraphM this Nothing
        rec = getPath >>= \case Left p -> subtractPath p >> rec; _ -> return ()
    rec
    unsafeFreeze residualGraphM

  traversal residualGraphM arr rec = \case
    (Visited pp, i) -> do
      lift$ unsafeWrite arr i Blind
      lift (unsafeRead residualGraphM i) >>= \case
        Just (Just back) -> for_ (nodes `unsafeAt` back) (recBackDown back) >> rec' back
        Just _ -> return ()
        _ | sinkFlags `unsafeAt` i -> throwE$ pp `appEndo` [i]
          | otherwise -> for_ (nodes `unsafeAt` i) recDown
      where
      rec' = rec . (Visited$ pp <> Endo (i:),)
      recDown j = unless (sourceFlags `unsafeAt` j)$ rec' j
      recBackDown back j = unless (sourceFlags `unsafeAt` j)$ rec'' j
        where rec'' = rec . (Visited$ pp <> Endo (\xs -> i:back:xs),)
    _ -> return ()


{-# INLINABLE minCut #-}
minCut :: Traversable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut nodes sources sinks = runST action where
  action :: forall s. ST s [Int]
  action = do
    let marks = isJust <$> maxFlow nodes sources sourceFlags sinkFlags
    let marks1 = ixedNodes & cataScan (_2 . traversed) %~ \(i, fb) ->
          marks `unsafeAt` i || or fb && not (sinkFlags `unsafeAt` i)

    let setter rec = \(g, i) -> let overmined = marks `unsafeAt` i || getAny g in
          overmined <$ for_ (nodes `unsafeAt` i) (rec . (Any overmined,))
    marks2Init :: STArray s Int Any <- newArray (bounds nodes) (Any False)
    marks2M :: STArray s Int Bool <- marks2Init & anaScanT2 setter return
    marks2 <- unsafeFreeze marks2M

    if all (marks1 `unsafeAt`) sinks  -- topmost min cut: all (marks2 `unsafeAt`) sources
      then return sinks  -- topmost min cut: return sources
      else do
        let newSources = map head$ group$ sort
              [ j
              | (i, node) <- elems ixedNodes
              , area `unsafeAt` i && not (marks2 `unsafeAt` i)
              , j <- toList node
              , marks2 `unsafeAt` j && not (sourceFlags `unsafeAt` j)
              ]
        let newSinks = map head$ group$ sort
              [ i
              | (i, node) <- elems ixedNodes
              , marks1 `unsafeAt` i && not (sinkFlags `unsafeAt` i)
              , any (\j -> area `unsafeAt` j && not (marks1 `unsafeAt` j)) node
              ]
        let sources' = filter (unsafeAt @Array marks2) sources ++ newSources
        let sinks' = filter (marks1 `unsafeAt` ) sinks ++ newSinks
        return$ minCut nodes sources' sinks'

  ixedNodes = listArray (bounds nodes)$ zip [0..] (elems nodes)

  sinkFlags = unsafeAccumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sinks
  sourceFlags = unsafeAccumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sources

  aboveSinks = ixedNodes & cataScan (_2 . traversed) %~ \(i, fb) -> sinkFlags `unsafeAt` i || or fb
  underSources = runST action where
    action :: forall s. ST s (Array Int Bool)
    action = do
      let setter rec = \(g, i) -> let overmined = sourceFlags `unsafeAt` i || getAny g in
            overmined <$ for_ (nodes `unsafeAt` i) (rec . (Any overmined,))
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

{-# INLINABLE minCut2Lowest #-}
minCut2Lowest :: Foldable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut2Lowest nodes sources sinks =
  map revIx$ minCut2HighestFFI revNodes revSources revSinks
  where
  bnds = bounds nodes
  maxIx = snd bnds
  revIx = (maxIx -)
  revNodes = ixmap bnds revIx$ runST action where
    action :: forall s. ST s (Array Int [Int])
    action = do
      preds :: STArray s Int [Int] <- newArray bnds []
      for_ (assocs nodes)$ \(i, node) ->
        for_ node$ \j -> unsafeRead preds j >>= unsafeWrite preds j . (revIx i :)
      unsafeFreeze preds
  revSources = map revIx sinks
  revSinks = map revIx sources

{-# INLINABLE minCut2Highest #-}
minCut2Highest :: Foldable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut2Highest nodes sources sinks =
  [ i
  | (i, Visited2) <- assocs reachablePart
  , sinkFlags `unsafeAt` i || any (\j -> reachablePart `unsafeAt` j == Unvisited2) (nodes `unsafeAt` i)
  ]
  where
  bnds = bounds nodes
  residualGraph = maxFlow nodes sources sourceFlags sinkFlags

  sinkFlags = unsafeAccumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sinks
  sourceFlags = unsafeAccumArray (\_ _ -> True) False (bounds nodes)$ map (, ()) sources

  reachablePart = runST action where
    action :: forall s. ST s (Array Int Path2)
    action = do
      arr <- newArray @(STArray s) (bounds nodes) Unvisited2
      for_ sources$
        flip dfs arr$ \rec -> let rec' = rec . (Unvisited2,) in \case
          (Unvisited2, i) -> do
            unsafeWrite arr i Visited2
            case residualGraph `unsafeAt` i of
              Just (Just back) -> for_ (nodes `unsafeAt` back) rec' >> rec' back
              Just _ -> return ()
              _ -> for_ (nodes `unsafeAt` i) rec'
          (_, i) -> return ()
      unsafeFreeze arr

{-# INLINABLE enumerateEdges #-}
enumerateEdges :: Foldable f => Array Int (f Int) -> ([Int], [Word])
enumerateEdges arr = runIdentity$ runNoConsT$ do
  arr' <- for arr$ \edges ->
    case toList edges of
      [] -> nocons maxBound
      xs -> head <$> for xs (nocons . fromIntegral)
  backstop <- nocons maxBound
  return$ elems arr' ++ [backstop]

-- FFI is somehow badly set up. Comment the following and use minCut2Highest for profiling...

foreign import ccall "automata_safa.h min_cut_highest" min_cut_highest_ffi
  :: Word -> Ptr Word
  -> Word -> Ptr Word
  -> Word -> Ptr Word
  -> Word -> Ptr Word
  -> Ptr (Ptr Word)
  -> IO Word

foreign import ccall "automata_safa.h &free_min_cut_highest" free_min_cut_highest_ffi
  :: FunPtr (Ptr Word -> IO ())

{-# INLINABLE minCut2HighestFFI #-}
minCut2HighestFFI :: Foldable f => Array Int (f Int) -> [Int] -> [Int] -> [Int]
minCut2HighestFFI nodes sources sinks = unsafePerformIO$ do
  if False
    then error$ show (sourcesC, sinksC)
    else do
      cutPtr <- mallocForeignPtr
      withForeignPtr cutPtr$ \cutPtr ->
        CA.withCArray nodesC$ \nodesPtr ->
        CA.withCArray edgesC$ \edgesPtr ->
        CA.withCArray sourcesC$ \sourcesPtr ->
        CA.withCArray sinksC$ \sinksPtr -> do
          cutSize <- min_cut_highest_ffi
            (fromIntegral$ CA.size nodesC) nodesPtr
            (fromIntegral$ CA.size edgesC) edgesPtr
            (fromIntegral$ CA.size sourcesC) sourcesPtr
            (fromIntegral$ CA.size sinksC) sinksPtr
            cutPtr
          cutPtr' <- peek cutPtr
          cutPtr'' <- newForeignPtr free_min_cut_highest_ffi cutPtr'
          cutC <- CA.unsafeForeignPtrToCArray cutPtr'' (0, cutSize - 1)
          return$ map fromIntegral$ CA.elems cutC
  where
  (nodes', edges) = enumerateEdges nodes
  nodesC = CA.listArray (0, numElements nodes + 1)$ map fromIntegral nodes'
  edgesC = CA.listArray (0, length edges - 1) edges
  sourcesC = CA.listArray (0, length sources - 1)$ map fromIntegral sources
  sinksC = CA.listArray (0, length sinks - 1)$ map fromIntegral sinks
