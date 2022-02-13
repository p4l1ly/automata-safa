{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DepDict where

import Data.Kind (Constraint, Type)
import GHC.TypeLits (Symbol)

data Got k = NotFound Symbol | Found k
data Named k = Name Symbol k

type family FromFound (x :: Got k) :: k where
  FromFound (Found x) = x

data DepDict where
  End :: DepDict
  (:|:) :: Named b -> DepDict -> DepDict
infixr 1 :|:

type family (:||:) (dict1 :: DepDict) (dict2 :: DepDict) :: DepDict where
  End :||: dict2 = dict2
  (x :|: dict1) :||: dict2 = x :|: dict1 :||: dict2

infixl 2 :||:

type family Remove (sym :: Symbol) (dict :: DepDict) :: DepDict where
  Remove _ End = End
  Remove sym (Name sym constr :|: rest) = Remove sym rest
  Remove sym (x :|: rest) = x :|: Remove sym rest

type family Get (sym :: Symbol) (dict :: DepDict) :: Got k where
  Get sym End = NotFound sym
  Get sym (Name sym constr :|: rest) = Found constr
  Get sym (_ :|: rest) = Get sym rest

type family Rename (old :: Symbol) (new :: Symbol) (k :: *) (dict :: DepDict) :: DepDict where
  Rename old new k dict = Name new (FromFound (Get old dict) :: k) :|: Remove old dict

type family Modify (sym :: Symbol) (mod :: k -> k') (dict :: DepDict) :: DepDict where
  Modify sym mod dict = Name sym (mod (FromFound (Get sym dict))) :|: Remove sym dict

type family ToConstraint (constrainable :: k) :: Constraint

type instance ToConstraint End = ()
type instance ToConstraint (Name _ c :|: rest) = (ToConstraint c, ToConstraint rest)
type instance ToConstraint (c :: Constraint) = c
