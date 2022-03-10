{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shaper where

import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (Reader, ReaderT (ReaderT, runReaderT), asks, local, runReader)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Fix (Fix (Fix))
import Data.Kind (Constraint)
import Lift (Lift)
import LiftTH (makeLiftable)

data IsTree (k :: *)

type family Ref (k :: *) (x :: *) :: *

type family MfnA (k :: *) :: *
type family MfnB (k :: *) :: *

type instance MfnA (Lift k) = MfnA k
type instance MfnB (Lift k) = MfnB k

data MfnK (k :: *) (a :: *) (b :: *)
type instance MfnA (MfnK _ a _) = a
type instance MfnB (MfnK _ _ b) = b

class Monad m => MonadFn (k :: *) (m :: * -> *) where
  monadfn :: MfnA k -> m (MfnB k)
makeLiftable ''MonadFn

type MonadFn' k a b m = (MonadFn k m, b ~ MfnB k, a ~ MfnA k)
type Ask k a m = MonadFn' k () a m

ask :: forall k a m. (Ask k a m) => m a
ask = monadfn @k ()

type family RecTrans (k :: *) :: * -> (* -> *) -> * -> *
type family RecRef (k :: *) :: *
type family RecFun (k :: *) :: *
type family RecVal (k :: *) :: *

data RecK (k :: *) (r :: *) (fr :: *) (a :: *)
type instance RecRef (RecK _ r _ _) = r
type instance RecFun (RecK _ _ fr _) = fr
type instance RecVal (RecK _ _ _ a) = a

class
  ( MonadFn (MfnK k (RecRef k) (RecVal k)) (RecTrans k (RecVal k) m)
  , MonadTrans (RecTrans k (RecVal k))
  , Monad (RecTrans k (RecVal k) m)
  , Monad m
  ) =>
  Recur (k :: *) (m :: * -> *)
  where
  recur :: (RecFun k -> RecTrans k (RecVal k) m (RecVal k)) -> RecRef k -> m (RecVal k)

type RecRecur k m =
  ( MonadFn (MfnK k () (RecRef k)) (RecTrans k (RecVal k) m)
  , Recur k m
  )

type family FRecRef (k :: *) :: *
type family FRecRef' (k :: *) :: *
type family FRecFun (k :: *) :: *

data FRecK (k :: *) (r :: *) (r' :: *) (fun :: *)
type instance FRecRef (FRecK _ r _ _) = r
type instance FRecRef' (FRecK _ _ r' _) = r'
type instance FRecFun (FRecK _ _ _ fun) = fun

class FunRecur (k :: *) (m :: * -> *) where
  funRecur :: FRecFun k -> m (FRecRef k -> m (FRecRef' k))

----------------------------------------------------------------------------------------

type FixRecurBody f a m = ReaderT (f (Fix f) -> FixRecurT f a m a, Fix f) m
newtype FixRecurT f a m r = FixRecurT (FixRecurBody f a m r)
  deriving (Functor, Applicative, Monad) via FixRecurBody f a m
type FixRecur f a = FixRecurT f a Identity

instance MonadTrans (FixRecurT f a) where
  lift action = FixRecurT (lift action)

runFixRecurT :: (f (Fix f) -> FixRecurT f a m a) -> Fix f -> m a
runFixRecurT rec x@(Fix f) = runReaderT (let FixRecurT m = rec f in m) (rec, x)

runFixRecur :: (f (Fix f) -> FixRecurT f a Identity a) -> Fix f -> a
runFixRecur rec x@(Fix f) = runIdentity $ runReaderT (let FixRecurT m = rec f in m) (rec, x)

-- instance Read "rec" (Fix f) (FixRecur f a) where
--   self = FixRecurT do asks snd
--
-- instance Inspect () (Fix f) a (FixRecur f a) where
--   inspect x@(Fix f) = do
--     rec <- FixRecurT do asks fst
--     let FixRecurT action = rec f
--     FixRecurT do local (\(rec, _) -> (rec, x)) action
--
-- data ReadFix f
-- instance Monad m => Inspect (ReadFix f) (Fix f) (f (Fix f)) m where
--   inspect (Fix f) = return f
--
-- instance Build () (Fix f) (f (Fix f)) (FixRecur f a) where
--   build = return . Fix
