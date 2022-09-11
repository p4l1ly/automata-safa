{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Afa.Finalful.STerm where

import Data.Functor.Classes (Eq1, Show1)
import GHC.Generics (Generic, Generic1)
import Generic.Data (Generically1 (..))
import Generic.Data.Orphans ()

type family Creation (way :: *) (input :: *) :: *

class Create (way :: *) (input :: *) where
  create :: input -> Creation way input

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

data QVR = Q | V | R

type Ctx = (Maybe *, Maybe *, Maybe *)
data ConstFn (x :: *) (y :: Ctx -> Ctx -> *) (inctx :: Ctx) (outctx :: Ctx)

type family OneshotNext (inctx :: Ctx) (ctx :: Ctx) (f :: [QVR]) (x :: Ctx -> Ctx -> *) :: * where
  OneshotNext inctx ctx '[] x = FunSelector (x inctx ctx)
-- q
  OneshotNext inctx '(Just q, v, r) (Q ': f) (ConstFn (q -> q') x') = OneshotNext inctx '(Just q', v, r) f x'
  OneshotNext '(_, v0, r0) '(Nothing, v, r) (Q ': f) (ConstFn (q -> q') x') = OneshotNext '(Just q, v0, r0) '(Just q', v, r) f x'
-- v
  OneshotNext inctx '(q, Just v, r) (V ': f) (ConstFn (v -> v') x') = OneshotNext inctx '(q, Just v', r) f x'
  OneshotNext '(q0, _, r0) '(q, Nothing, r) (V ': f) (ConstFn (v -> v') x') = OneshotNext '(q0, Just v, r0) '(q, Just v', r) f x'
-- r
  OneshotNext inctx '(q, v, Just r) (R ': f) (ConstFn (r -> r') x') = OneshotNext inctx '(q, v, Just r') f x'
  OneshotNext '(q0, v0, _) '(q, v, Nothing) (R ': f) (ConstFn (r -> r') x') = OneshotNext '(q0, v0, Just r) '(q, v, Just r') f x'

type family FunSelector (x :: *) :: *

data OneshotFunSelector (inctx :: Ctx) (outctx :: Ctx)
data OneshotTraSelector (m :: * -> *) (inctx :: Ctx) (outctx :: Ctx)

type family OneshotFunInput (input :: *) :: Ctx -> Ctx -> * where
  OneshotFunInput (fn :&: c) = ConstFn fn (OneshotFunInput c)
  OneshotFunInput fn = ConstFn fn OneshotFunSelector

type family OneshotTraInput (input :: *) :: Ctx -> Ctx -> * where
  OneshotTraInput ((a -> m b) :&: c) = ConstFn (a -> b) (OneshotTraInput c)
  OneshotTraInput (a -> m b) = ConstFn (a -> b) (OneshotTraSelector m)

data OneshotFun (mfun :: [QVR])
data OneshotTra (mfun :: [QVR])

type instance
  Creation (OneshotFun (mfun :: [QVR])) input =
    OneshotNext '(Nothing, Nothing, Nothing) '(Nothing, Nothing, Nothing) mfun (OneshotFunInput input)

type instance
  Creation (OneshotTra (mfun :: [QVR])) input =
    OneshotNext '(Nothing, Nothing, Nothing) '(Nothing, Nothing, Nothing) mfun (OneshotTraInput input)

data a :&: b = a :&: b
infixr 0 :&:

data QVFun q v q' v' = QVFun (q -> q') (v -> v')
newtype QFun q q' = QFun (q -> q')
newtype RTra (m :: * -> *) (r :: *) (r' :: *) = RTra (r -> m r')
newtype VarTra (m :: * -> *) (v :: *) (q :: *) (v' :: *) (r' :: *) = VarTra (v -> m (Term q v' r'))
data QVTra (m :: * -> *) (q :: *) (v :: *) (q' :: *) (v' :: *) (r' :: *)
  = QVTra (q -> m (Term q' v' r')) (v -> m (Term q' v' r'))

type instance
  FunSelector
    (OneshotFunSelector '(Just q, Just v, Nothing) '(Just q', Just v', Nothing)) =
    QVFun q v q' v'
type instance
  FunSelector
    (OneshotFunSelector '(Just q, Nothing, Nothing) '(Just q', Nothing, Nothing)) =
    QFun q q'
type instance
  FunSelector
    (OneshotTraSelector m '(Nothing, Nothing, Just r) '(Nothing, Nothing, Just r')) =
    RTra m r r'

instance Create (OneshotFun [Q, V]) ((q -> q') :&: (v -> v')) where
  create (qfn :&: vfn) = QVFun qfn vfn

instance Create (OneshotFun '[Q]) (q -> q') where
  create qfn = QFun qfn

instance Create (OneshotTra '[R]) (r -> m r') where
  create rfn = RTra rfn

testFun :: Num b => QVFun a String b Bool
testFun = create @(OneshotFun [Q, V]) $ const 5 :&: (== "foo")

testTra :: forall m r. Monad m => RTra m r r
testTra = create @(OneshotTra '[R]) return
