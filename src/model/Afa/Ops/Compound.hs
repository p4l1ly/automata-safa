module Afa.Ops.Compound
  ( simpGoblinMincut
  , simpGoblinMincutUntilFixpoint
  , simpGoblin
  , simpMincut
  ) where

import Debug.Trace

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
