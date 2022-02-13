{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Afa.Finalful.STerm where

import Create (Apply)
import Data.Composition ((.:))
import Data.Functor.Classes (Eq1, Show1)
import GHC.Generics (Generic, Generic1)
import Generic.Data (Generically1 (..))
import Generic.Data.Orphans ()

data Term q v r
  = LTrue
  | LFalse
  | State !q
  | Var !v
  | Not !r
  | And !r !r
  | Or !r !r
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1)
  deriving (Eq1, Show1) via (Generically1 (Term q v))

data MFun = E * * * | Q * MFun | V * MFun | R * MFun

type family In (fun :: MFun) :: * where
  In (E q v r) = (q, v, r)
  In (Q _ fun) = In fun
  In (V _ fun) = In fun
  In (R _ fun) = In fun

infixr 9 `Q`
infixr 9 `V`
infixr 9 `R`

type family Fst (t :: (*, *, *)) :: * where
  Fst '(a, b, c) = a

type family Snd (t :: (*, *, *)) :: * where
  Snd '(a, b, c) = b

type family Trd (t :: (*, *, *)) :: * where
  Trd '(a, b, c) = c

type family Out (fun :: MFun) :: (*, *, *) where
  Out (E q v r) = '(q, v, r)
  Out (Q q fun) = '(q, Snd (Out fun), Trd (Out fun))
  Out (V v fun) = '(Fst (Out fun), v, Trd (Out fun))
  Out (R r fun) = '(Fst (Out fun), Snd (Out fun), r)

type instance Apply (E _ _ _) result = result
type instance Apply (Q q fun) result = (Fst (Out fun) -> q) -> Apply fun result
type instance Apply (V v fun) result = (Snd (Out fun) -> v) -> Apply fun result
type instance Apply (R r fun) result = (Trd (Out fun) -> r) -> Apply fun result
