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
