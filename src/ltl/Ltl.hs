{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}

module Ltl where

import Control.Monad.Free (Free(..))
import Data.Bifunctor
import GHC.Generics
import Data.Functor.Classes
import Data.Functor.Foldable
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Hashable
import Data.Hashable.Lifted

import Ltl.Lib (bloom, skippingAlg)


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


deRelease :: Ltl t -> Ltl (Free Ltl t)
deRelease (Release x y) = WeakUntil (Pure y) (Free$ And [Pure x, Pure y])
deRelease x = fmap Pure x


pushNeg :: (Bool, Ltl t) -> Free Ltl (Bool, t)
pushNeg (b, Not t) = Pure (not b, t)
pushNeg (False, And ts) = Free$ Or$ map (Pure . (False,)) ts
pushNeg (False, Or ts) = Free$ And$ map (Pure . (False,)) ts
pushNeg (False, Var i) = Free$ Not$ Free$ Var i
pushNeg (False, LTrue) = Free LFalse
pushNeg (False, LFalse) = Free LTrue
pushNeg (b, f) = Free$ fmap (Pure . (b,)) f


preprocess :: (Bool, Ltl t) -> Free Ltl (Bool, t)
preprocess = bloom (Free . deRelease) . pushNeg


preprocessCoRecursive :: (Recursive t, Corecursive t, Ltl ~ Base t) => t -> t
preprocessCoRecursive = futu (skippingAlg$ preprocess . second project) . (True,)
