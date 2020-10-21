{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}

module Ltl where

import GHC.Generics
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Foldable
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable
import Data.Hashable.Lifted

data Ltl rec
  = Var Int
  | LTrue
  | LFalse
  | And [rec]
  | Or [rec]
  | Not rec
  | Next rec
  | Until rec rec
  | WeakUntil rec rec
  | Globally rec
  | Finally rec
  | Release rec rec
  deriving
    (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1, Hashable, Hashable1)
  deriving Show1 via (Generically1 Ltl)


deRelease_alg :: (Corecursive t, Ltl ~ Base t) => Ltl t -> t
deRelease_alg (Release x y) = embed$ WeakUntil y (embed$ And [x, y])
deRelease_alg x = embed x


pushNeg_cocoalg :: (Corecursive t, Recursive t, Ltl ~ Base t)
  => (Bool, Ltl t) -> Ltl (Bool, t)
pushNeg_cocoalg (b, Not t) = pushNeg_cocoalg (not b, project t)
pushNeg_cocoalg (False, And ts) = Or$ map (False,) ts
pushNeg_cocoalg (False, Or ts) = And$ map (False,) ts
pushNeg_cocoalg (False, Var i) = Not (True, embed$ Var i)
pushNeg_cocoalg (False, LTrue) = LFalse
pushNeg_cocoalg (False, LFalse) = LTrue
pushNeg_cocoalg (b, f) = fmap (b,) f


allVars_alg :: Ltl [Int] -> [Int]
allVars_alg (Var i) = [i]
allVars_alg f = Data.Foldable.fold f
