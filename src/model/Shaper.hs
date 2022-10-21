{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Shaper where

import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Reader (Reader, ReaderT (ReaderT, runReaderT), asks, local, runReader)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Fix (Fix (Fix))
import Data.Kind (Constraint)
import InversionOfControl.Lift (K (K), LiftCount, Pean (Succ, Zero), Unwrap)

class MLift (n :: Pean) (m' :: * -> *) (m :: * -> *) where
  mlift :: m a -> m' a

instance (MLift n m' m, MonadTrans mt, Monad m') => MLift (Succ n) (mt m') m where
  mlift (ma :: m a) = lift (mlift @n @m' @m ma :: m' a)

instance MLift n m m where
  mlift = id

type family MfnA (k :: *) :: *
type family MfnB (k :: *) :: *

data MfnK (a :: *) (b :: *) (k :: *)
type instance MfnA (MfnK a _ _) = a
type instance MfnB (MfnK _ b _) = b

data IsTree (k :: *)
type instance MfnA (IsTree _) = ()
type instance MfnB (IsTree _) = Bool

class Monad m => MonadFn (k :: K) (m :: * -> *) where
  monadfn :: MfnA (Unwrap k) -> m (MfnB (Unwrap k))

instance
  (MonadFn ( 'K n k) m, MonadTrans mt, Monad m, Monad (mt m)) =>
  MonadFn ( 'K (Succ n) k) (mt m)
  where
  monadfn p1 = lift (monadfn @( 'K n k) p1)

type MonadFn' k a b m = (MonadFn k m, b ~ MfnB (Unwrap k), a ~ MfnA (Unwrap k))
type Ask k a m = MonadFn' k () a m

ask :: forall k a m. (Ask k a m) => m a
ask = monadfn @k ()

type family RecTrans (k :: *) :: * -> (* -> *) -> * -> *
type family RecRef (k :: *) :: *
type family RecFun (k :: *) :: *
type family RecVal (k :: *) :: *

data RecK (r :: *) (fr :: *) (a :: *) (n :: Pean) (k :: *)
type instance RecRef (RecK r _ _ _ _) = r
type instance RecFun (RecK _ fr _ _ _) = fr
type instance RecVal (RecK _ _ a _ _) = a

class Recur0 (k :: K) (m :: * -> *) where
  recur ::
    ( RecFun (Unwrap k) ->
      RecTrans (Unwrap k) (RecVal (Unwrap k)) m (RecVal (Unwrap k))
    ) ->
    m (RecRef (Unwrap k) -> m (RecVal (Unwrap k)))

type Recur (k :: K) (m :: * -> *) = Recur1 k m (Unwrap k)
type Recur1 (k :: K) (m :: * -> *) (x :: *) =
  ( MonadFn ( 'K Zero (MfnK (RecRef x) (RecVal x) x)) (RecTrans x (RecVal x) m)
  , MonadTrans (RecTrans x (RecVal x))
  , Monad (RecTrans x (RecVal x) m)
  , Monad m
  , Recur0 k m
  )

type RecRecur (k :: K) (m :: * -> *) = RecRecur1 k m (Unwrap k)
type RecRecur1 (k :: K) (m :: * -> *) (x :: *) =
  ( MonadFn ( 'K Zero (MfnK () (RecRef x) x)) (RecTrans x (RecVal x) m)
  , MonadFn ( 'K Zero (IsTree x)) (RecTrans x (RecVal x) m)
  , Recur k m
  )

type family FRecRef (k :: *) :: *
type family FRecRef' (k :: *) :: *
type family FRecFun (k :: *) :: *

data FRecK (r :: *) (r' :: *) (fun :: *) (k :: *)
type instance FRecRef (FRecK r _ _ _) = r
type instance FRecRef' (FRecK _ r' _ _) = r'
type instance FRecFun (FRecK _ _ fun _) = fun

class FunRecur (k :: K) (m :: * -> *) where
  funRecur :: FRecFun (Unwrap k) -> m (FRecRef (Unwrap k) -> m (FRecRef' (Unwrap k)))

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
