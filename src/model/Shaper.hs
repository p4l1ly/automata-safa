{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
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
import LiftTH (makeLiftable)

class Monad m => Ask (k :: *) a m | k m -> a where
  ask :: m a
makeLiftable ''Ask

class Monad m => Transform (k :: *) a b m | k m -> a b where
  transform :: a -> m b
makeLiftable ''Transform

type family RecTrans (k :: *) (m :: * -> *) :: * -> (* -> *) -> * -> *
data Rec (k :: *) m
class
  ( Transform (Rec k m) r a (RecTrans k m a m)
  , MonadTrans (RecTrans k m a)
  , Monad (RecTrans k m a m)
  , Monad m
  ) =>
  Recur (k :: *) r fr a m
    | k m r -> fr a
  where
  recur :: (fr -> RecTrans k m a m a) -> r -> m a

type RecRecur k r fr a m = (Ask (Rec k m) r (RecTrans k m a m), Recur k r fr a m)

class FunRecur (k :: *) r r' fun m | k m r -> fun r' where
  funRecur :: fun -> m (r -> m r')

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
