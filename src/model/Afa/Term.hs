{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Afa.Term (
  Term (..),
  QVR (..),
  q,
  v,
  r,
  q1,
  v1,
  r1,
  qSelf,
  vSelf,
  rSelf,
  QVFun (..),
  QFun (..),
  RTra (..),
  VTra (..),
  QVTra (..),
  Create (create),
  Creation,
  OneshotFun,
  OneshotTra,
  OneshotNext,
  Ctx,
  Ctx0,
  OneshotFunInput,
  FunSelector,
  (:&:) ((:&:)),
  TermParam,
  MultiwayTerm(..),
  andMulti,
  orMulti,
  sameTraverse
) where

import Data.Functor.Classes (Eq1, Show1)
import Data.Hashable
import Data.Hashable.Lifted
import GHC.Generics (Generic, Generic1)
import Generic.Data (Generically1 (..))
import Generic.Data.Orphans ()
import InversionOfControl.TypeDict hiding (Name)
import Language.Haskell.TH hiding (Q, Type)
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import System.Random
import System.IO.Unsafe
import Afa.ShallowHashable
import Data.List
import qualified Data.HashSet as HS
import Data.Kind (Type)

type family Creation (way :: Type) (input :: Type) :: Type

class Create (way :: Type) (input :: Type) where
  create :: input -> Creation way input

data Term q v r
  = LTrue
  | LFalse
  | State !q
  | Var !v
  | Not !r
  | And !r !r
  | Or !r !r
  deriving (Functor, Foldable, Traversable, Show, Generic, Generic1)
  deriving (Show1) via (Generically1 (Term q v))

instance (Eq q, Eq v, Eq (Shallow r)) => Eq (Term q v r) where
  LTrue == LTrue = True
  LFalse == LFalse = True
  State q1 == State q2 = q1 == q2
  Var v1 == Var v2 = v1 == v2
  Not r1 == Not r2 = r1 `shallowEq` r2
  And r11 r12 == And r21 r22 = r11 `shallowEq` r21 && r12 `shallowEq` r22
  Or r11 r12 == Or r21 r22 = r11 `shallowEq` r21 && r12 `shallowEq` r22
  _ == _ = False

instance (Hashable q, Hashable v, Hashable (Shallow r)) => Hashable (Term q v r) where
  hashWithSalt salt LTrue = hashWithSalt' salt 988431
  hashWithSalt salt LFalse = hashWithSalt' salt 1438231
  hashWithSalt salt (State q) = hashWithSalt (hashWithSalt' salt 4331) q
  hashWithSalt salt (Var v) = hashWithSalt (hashWithSalt' salt 8183457) v
  hashWithSalt salt (Not r) = shallowHash (hashWithSalt' salt 9842714) r
  hashWithSalt salt (And r1 r2) = shallowHash (shallowHash (hashWithSalt' salt 4324142) r1) r2
  hashWithSalt salt (Or r1 r2) = shallowHash (shallowHash (hashWithSalt' salt 38914) r1) r2


data MultiwayTerm q v r
  = LTrueMulti
  | LFalseMulti
  | StateMulti !q
  | VarMulti !v
  | NotMulti !r
  | AndMulti !(HS.HashSet (Shallow r))
  | OrMulti !(HS.HashSet (Shallow r))
  deriving (Foldable, Show, Generic)
  -- deriving (Show1) via (Generically1 (MultiwayTerm q v))


sameTraverse :: (Applicative f, Hashable (Shallow b)) => (b -> f b) -> MultiwayTerm q v b -> f (MultiwayTerm q v b)
sameTraverse fn LTrueMulti = pure LTrueMulti
sameTraverse fn LFalseMulti = pure LFalseMulti
sameTraverse fn x@(StateMulti q) = pure x
sameTraverse fn x@(VarMulti v) = pure x
sameTraverse fn (NotMulti r) = NotMulti <$> fn r
sameTraverse fn (AndMulti r) = do
  AndMulti . HS.fromList . map Shallow <$> traverse (fn . unshallow) (HS.toList r)
sameTraverse fn (OrMulti r) =
  OrMulti . HS.fromList . map Shallow <$> traverse (fn . unshallow) (HS.toList r)


andMulti :: (Eq (Shallow r), Hashable (Shallow r)) => [r] -> MultiwayTerm q v r
andMulti = AndMulti . HS.fromList . map Shallow
orMulti :: (Eq (Shallow r), Hashable (Shallow r)) => [r] -> MultiwayTerm q v r
orMulti = OrMulti . HS.fromList . map Shallow

type family TermParam (sel :: QVR) (t :: Type) :: Type where
  TermParam Q (Term q v r) = q
  TermParam V (Term q v r) = v
  TermParam R (Term q v r) = r
  TermParam Q (MultiwayTerm q v r) = q
  TermParam V (MultiwayTerm q v r) = v
  TermParam R (MultiwayTerm q v r) = r

instance (Eq q, Eq v, Eq (Shallow r)) => Eq (MultiwayTerm q v r) where
  LTrueMulti == LTrueMulti = True
  LFalseMulti == LFalseMulti = True
  StateMulti q1 == StateMulti q2 = q1 == q2
  VarMulti v1 == VarMulti v2 = v1 == v2
  NotMulti r1 == NotMulti r2 = r1 `shallowEq` r2
  AndMulti rs1 == AndMulti rs2 = rs1 == rs2
  OrMulti rs1 == OrMulti rs2 = rs1 == rs2
  _ == _ = False

instance (Hashable q, Hashable v, Hashable (Shallow r)) => Hashable (MultiwayTerm q v r) where
  hashWithSalt salt LTrueMulti = hashWithSalt' salt 1454735963
  hashWithSalt salt LFalseMulti = hashWithSalt' salt 434085917
  hashWithSalt salt (StateMulti q) = hashWithSalt (hashWithSalt' salt 2844348065) q
  hashWithSalt salt (VarMulti v) = hashWithSalt (hashWithSalt' salt 13096731) v
  hashWithSalt salt (NotMulti r) = shallowHash (hashWithSalt' salt 4545191) r
  hashWithSalt salt (AndMulti rs) = foldl' hashWithSalt (hashWithSalt' salt 693727) rs
  hashWithSalt salt (OrMulti rs) = foldl' hashWithSalt (hashWithSalt' salt 943218321) rs

paramGetter :: String -> Name -> TypeQ
paramGetter dname x = do
  d <- lookupTypeName dname
  case d of
    Just d ->
      return $
        let followD = AppT (ConT ''Follow) (VarT d)
            getTerm = AppT (AppT (ConT ''Get) (LitT (StrTyLit "term")))
            param = AppT (AppT (ConT ''TermParam) (ConT x))
         in param (getTerm followD)
    Nothing -> error "paramGetter: type d not in scope"

q :: TypeQ
v :: TypeQ
r :: TypeQ
q = paramGetter "d" 'Q
v = paramGetter "d" 'V
r = paramGetter "d" 'R

q1 :: TypeQ
v1 :: TypeQ
r1 :: TypeQ
q1 = paramGetter "d1" 'Q
v1 = paramGetter "d1" 'V
r1 = paramGetter "d1" 'R

paramGetterSelf :: Name -> TypeQ
paramGetterSelf x = do
  return $
    let followD = AppT (ConT ''Follow) (ConT ''Self)
        getTerm = AppT (AppT (ConT ''Get) (LitT (StrTyLit "term")))
        param = AppT (AppT (ConT ''TermParam) (ConT x))
     in param (getTerm followD)

qSelf :: TypeQ
vSelf :: TypeQ
rSelf :: TypeQ
qSelf = paramGetterSelf 'Q
vSelf = paramGetterSelf 'V
rSelf = paramGetterSelf 'R

data QVR = Q | V | R
