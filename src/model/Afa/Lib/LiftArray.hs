{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Afa.Lib.LiftArray where

import Control.Monad.Trans
import Data.Array.Base
import Data.Array.ST

newtype LiftArray a i e = LiftArray {unLiftArray :: a i e}

instance (MonadTrans mt, Monad (mt m), MArray a e m)
  => MArray (LiftArray a) e (mt m) where
  {-# INLINE getBounds #-}
  getBounds (LiftArray arr) = lift$ getBounds arr
  {-# INLINE unsafeRead #-}
  unsafeRead (LiftArray arr) i = lift$ unsafeRead arr i
  {-# INLINE unsafeWrite #-}
  unsafeWrite (LiftArray arr) i v = lift$ unsafeWrite arr i v
  {-# INLINE getNumElements #-}
  getNumElements (LiftArray arr) = lift$ getNumElements arr
  {-# INLINE newArray #-}
  newArray bnds e = LiftArray<$> lift (newArray bnds e)
  {-# INLINE newArray_ #-}
  newArray_ bnds = LiftArray<$> lift (newArray_ bnds)
  {-# INLINE unsafeNewArray_ #-}
  unsafeNewArray_ bnds = LiftArray<$> lift (unsafeNewArray_ bnds)


type LSTArray s = LiftArray (STArray s)
type LLSTArray s = LiftArray (LSTArray s)
type LLLSTArray s = LiftArray (LLSTArray s)
