module Afa.Ops.Compound where

import Debug.Trace
import Data.Hashable

import Afa.Bool
import Afa.Ops.Goblin
import Afa.Ops.QMinCut

simpGoblinMincut :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpGoblinMincut bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  bafa@(BoolAfa _ afa) <- simplifyAll bafa{afa = goblinUntilFixpoint afa}
  simplifyAll bafa{afa = qminCut afa}

simpGoblin :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpGoblin bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  simplifyAll bafa{afa = goblinUntilFixpoint afa}

simpMincut :: (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simpMincut bafa = do
  bafa@(BoolAfa _ afa) <- simplifyAll bafa
  simplifyAll bafa{afa = qminCut afa}
