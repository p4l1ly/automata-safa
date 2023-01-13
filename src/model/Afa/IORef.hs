{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.IORef where

import Control.Monad.IO.Class
import Data.Function.Apply
import qualified Data.HashMap.Strict as HM
import Data.IORef
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import System.Mem.StableName

type FR f = f (Ref f)
type R f = IORef (FR f)
type SN f = StableName (R f)
type S f = (SN f, R f)
data Ref f = Ref (S f) | Subtree (FR f)

data Build
data Share
data Deref
data IsTree

instance MonadFn ('K Zero (Explicit (Ref f) Bool IsTree)) IO where
  monadfn (Ref _) = return False
  monadfn (Subtree f) = return True

instance MonadFn ('K Zero (Explicit (Ref f) (f (Ref f)) Deref)) IO where
  monadfn (Ref (_, ioref)) = liftIO $ readIORef ioref
  monadfn (Subtree f) = return f

instance MonadFn ('K Zero (Explicit (f (Ref f)) (Ref f) Build)) IO where
  monadfn f = return $ Subtree f

instance MonadFn ('K Zero (Explicit (Ref f) (Ref f) Share)) IO where
  monadfn (Subtree f) = do
    ioref <- liftIO $ newIORef f
    name <- liftIO $ makeStableName ioref
    return $ Ref (name, ioref)
  monadfn r = return r

runRecur :: MonadIO m' => ((Ref f -> m' b) -> FR f -> m' b) -> ((Ref f -> m' b) -> IO a) -> IO a
runRecur getAlgebra getAction = do
  cacheRef <- newIORef HM.empty
  let recur r = do
        case r of
          Subtree f -> getAlgebra recur f
          Ref (name, ioref) -> do
            cache <- liftIO $ readIORef cacheRef
            case HM.lookup name cache of
              Just b -> return b
              Nothing -> do
                f <- liftIO $ readIORef ioref
                result <- getAlgebra recur f
                liftIO $ modifyIORef' cacheRef (HM.insert name result)
                return result
  getAction recur

data IORefO (cont :: *) (n :: Pean)
type instance
  Definition (IORefO cont n) =
    Name "build" ('K n Build)
      :+: Name "share" ('K n Share)
      :+: Name "deref" ('K n Deref)
      :+: Name "isTree" ('K n IsTree)
      :+: Follow cont
