{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Afa.Finalful.STerm where

import Create (Apply, Create (create))
import Data.Composition ((.:))
import Data.Functor.Classes (Eq1, Show1)
import GHC.Generics (Generic, Generic1)
import Generic.Data (Generically1 (..))
import Generic.Data.Orphans ()

type family Fst (t :: (*, *, *)) :: * where
  Fst '(a, b, c) = a

type family Snd (t :: (*, *, *)) :: * where
  Snd '(a, b, c) = b

type family Trd (t :: (*, *, *)) :: * where
  Trd '(a, b, c) = c

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

type family In (fun :: MFun) :: (*, *, *) where
  In (E q v r) = '(q, v, r)
  In (Q _ fun) = In fun
  In (V _ fun) = In fun
  In (R _ fun) = In fun

infixr 9 `Q`
infixr 9 `V`
infixr 9 `R`

type family Out (fun :: MFun) :: (*, *, *) where
  Out (E q v r) = '(q, v, r)
  Out (Q q fun) = '(q, Snd (Out fun), Trd (Out fun))
  Out (V v fun) = '(Fst (Out fun), v, Trd (Out fun))
  Out (R r fun) = '(Fst (Out fun), Snd (Out fun), r)

type instance Apply (E _ _ _) result = result
type instance Apply (Q q fun) result = (Fst (Out fun) -> q) -> Apply fun result
type instance Apply (V v fun) result = (Snd (Out fun) -> v) -> Apply fun result
type instance Apply (R r fun) result = (Trd (Out fun) -> r) -> Apply fun result

data MTra = MTra MFun (* -> *)

type family InTra (fun :: MTra) :: (*, *, *) where
  InTra ( 'MTra mfun _) = In mfun

type family OutTra (fun :: MTra) :: (*, *, *) where
  OutTra ( 'MTra mfun _) = Out mfun

type family MonadTra (fun :: MTra) :: (* -> *) where
  MonadTra ( 'MTra _ m) = m

type instance Apply ( 'MTra (E _ _ _) m) result = result
type instance Apply ( 'MTra (Q q fun) m) result = (Fst (Out fun) -> m q) -> Apply fun result
type instance Apply ( 'MTra (V v fun) m) result = (Snd (Out fun) -> m v) -> Apply fun result
type instance Apply ( 'MTra (R r fun) m) result = (Trd (Out fun) -> m r) -> Apply fun result

-- instances (for now, very incomplete)

data PerVarMFun fun
  = PerVarMFun
      (Fst (In fun) -> Fst (Out fun))
      (Snd (In fun) -> Snd (Out fun))
      (Trd (In fun) -> Trd (Out fun))
instance Create (q' `Q` v' `V` E q v r) (PerVarMFun (q' `Q` v' `V` E q v r)) where
  create qfn vfn = PerVarMFun qfn vfn id

data PerVarMTra fun
  = PerVarMTra
      (Fst (InTra fun) -> MonadTra fun (Fst (OutTra fun)))
      (Snd (InTra fun) -> MonadTra fun (Snd (OutTra fun)))
      (Trd (InTra fun) -> MonadTra fun (Trd (OutTra fun)))
instance
  Applicative m =>
  Create
    ( 'MTra (r' `R` E q v r) m)
    (PerVarMTra ( 'MTra (r' `R` E q v r) m))
  where
  create rfn = PerVarMTra pure pure rfn
