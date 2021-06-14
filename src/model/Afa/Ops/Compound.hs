{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}

module Afa.Ops.Compound
  ( simpGoblinMincut
  , simpGoblinMincutUntilFixpoint
  , simpGoblin
  , simpMincut
  ) where

import Debug.Trace

import Data.Foldable
import Data.String.Interpolate
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import Data.Array

import Data.Hashable

import Data.Array.Base (numElements)
import Afa (Afa(..))
import Afa.Bool
import Afa.Ops.Goblin2
import Afa.Ops.QMinCut

mincutUntilFixpoint :: (Eq p, Hashable p, Show p) =>
  BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
mincutUntilFixpoint bafa@(BoolAfa _ afa) = do
  bafa'@(BoolAfa _ afa') <- simplifyAll bafa{afa = qminCut afa}
  if traceShow (numElements (states afa'), numElements (states afa))
    numElements (states afa') < numElements (states afa)
    then mincutUntilFixpoint bafa'
    else return bafa'

{-# INLINABLE simpGoblinMincutUntilFixpoint #-}
simpGoblinMincutUntilFixpoint :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpGoblinMincutUntilFixpoint bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  bafa <- simplifyAll bafa{afa = goblinUntilFixpoint afa}
  mincutUntilFixpoint bafa

{-# INLINABLE simpGoblinMincut #-}
simpGoblinMincut :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpGoblinMincut bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  bafa@(BoolAfa _ afa) <- simplifyAll bafa{afa = goblinUntilFixpoint afa}
  simplifyAll bafa{afa = qminCut afa}

{-# INLINABLE simpGoblin #-}
simpGoblin :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpGoblin bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  simplifyAll bafa{afa = goblinUntilFixpoint afa}

{-# INLINABLE simpMincut #-}
simpMincut :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpMincut bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  mincutUntilFixpoint bafa

toDot :: Bool -> BoolAfaUnswallowed Int -> String
toDot cyclic (BoolAfa bterms (Afa mterms states init)) = unlines
  [ "digraph afa {"
  , "  graph [nodesep=0.2];"
  , "  node [fontsize=20];"
  , unlines [[i|  b#{j} -> #{c};|] | (j, t) <- assocs bterms, c <- bchilds t]
  , unlines [[i|  m#{j} -> #{c};|] | (j, t) <- assocs mterms, c <- mchilds t]
  , unlines [[i|  q#{j} -> m#{q}|] | (j, q) <- assocs states]
  , unlines [[i|  q#{j} [style=filled, fillcolor=pink]|] | (j, _) <- assocs states]
  , unlines [[i|  b#{j} [style=filled, #{bstyle j t}]|] | (j, t) <- assocs bterms]
  , unlines [[i|  m#{j} [style=filled, #{mstyle j t}]|] | (j, t) <- assocs mterms]
  , "}"
  ]
  where
    bchilds t = [[i|b#{c}|] | c <- toList t]
    mchilds t = case t of
      MTerm.Predicate p -> [[i|b#{p}|]]
      MTerm.State q -> if cyclic then [[i|q#{q}|]] else [[i|Q#{q}|]]
      _ -> [[i|m#{c}|] | c <- toList t]

    bstyle j (BTerm.Not _) = "shape=rectangle, fillcolor=indianred1"
    bstyle j (BTerm.And _) = "shape=rectangle, fillcolor=lightgoldenrod1"
    bstyle j (BTerm.Or _) = "shape=rectangle, fillcolor=lightblue"
    bstyle j (BTerm.Predicate p) = [i|shape=rectangle, fillcolor=yellow, label=b#{j}p#{p}|]
    bstyle j BTerm.LTrue = "shape=rectangle, fillcolor=green"
    bstyle j BTerm.LFalse = "shape=rectangle, fillcolor=red"

    mstyle j (MTerm.And _) = "shape=rectangle, fillcolor=lightgoldenrod1"
    mstyle j (MTerm.Or _) = "shape=rectangle, fillcolor=lightblue"
    mstyle j (MTerm.Predicate p) = [i|shape=rectangle, fillcolor=lightgrey, label=m#{j}p#{p}|]
    mstyle j (MTerm.State _) = "shape=rectangle, fillcolor=white"
    mstyle j MTerm.LTrue = "shape=rectangle, fillcolor=green"
