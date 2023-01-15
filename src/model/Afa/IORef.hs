{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.IORef where

import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Function.Apply
import qualified Data.HashMap.Strict as HM
import Data.IORef
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.MonadFn
import qualified InversionOfControl.Recur as R
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
data Cata
data RCata

instance MonadFn0 (Explicit (Ref f) Bool IsTree) IO where
  monadfn0 (Ref _) = return False
  monadfn0 (Subtree f) = return True

instance MonadFn0 (Explicit (Ref f) (f (Ref f)) Deref) IO where
  monadfn0 (Ref (_, ioref)) = readIORef ioref
  monadfn0 (Subtree f) = return f

instance MonadFn0 (Explicit (f (Ref f)) (Ref f) Build) IO where
  monadfn0 f = return $ Subtree f

instance MonadFn0 (Explicit (Ref f) (Ref f) Share) IO where
  monadfn0 (Subtree f) = do
    ioref <- newIORef f
    name <- makeStableName ioref
    return $ Ref (name, ioref)
  monadfn0 r = return r

type instance R.Et (R.Explicit ('K _ Cata) _ _ _) = IdentityT
instance
  (Monad m, LiftN n IO m) =>
  R.Recur (R.Explicit ('K n Cata) n' (Ref f) (FR f)) b m
  where
  runRecur getAlgebra getAction = do
    cacheRef <- liftn @n $ newIORef HM.empty
    let liftIO' :: IO a -> _ a
        liftIO' = liftn @n' @(IdentityT m) . lift . liftn @n
    let recur r = do
          case r of
            Subtree f -> getAlgebra recur f
            Ref (name, ioref) -> do
              cache <- liftIO' $ readIORef cacheRef
              case HM.lookup name cache of
                Just b -> return b
                Nothing -> do
                  f :: FR f <- liftIO' $ readIORef (ioref :: IORef (FR f))
                  result <- getAlgebra recur (f :: FR f)
                  liftIO' $
                    modifyIORef' cacheRef (HM.insert name result)
                  return result
    runIdentityT $ getAction recur

type instance R.Et (R.Explicit ('K _ RCata) _ _ _) = IdentityT
instance
  (Monad m, LiftN n IO m) =>
  R.Recur (R.Explicit ('K n RCata) n' (Ref f) (Ref f, FR f)) b m
  where
  runRecur getAlgebra getAction = do
    cacheRef <- liftn @n $ newIORef HM.empty
    let liftIO' :: IO a -> _ a
        liftIO' = liftn @n' @(IdentityT m) . lift . liftn @n
    let recur r = do
          case r of
            Subtree f -> getAlgebra recur (r, f)
            Ref (name, ioref) -> do
              cache <- liftIO' $ readIORef cacheRef
              case HM.lookup name cache of
                Just b -> return b
                Nothing -> do
                  f <- liftIO' $ readIORef ioref
                  result <- getAlgebra recur (r, f)
                  liftIO' $ modifyIORef' cacheRef (HM.insert name result)
                  return result
    runIdentityT $ getAction recur

data IORefO (cont :: *) (n :: Pean)
type instance
  Definition (IORefO cont n) =
    Name "build" ('K n Build)
      :+: Name "share" ('K n Share)
      :+: Name "deref" ('K n Deref)
      :+: Name "isTree" ('K n IsTree)
      :+: Name "cata" ('K n Cata)
      :+: Name "rcata" ('K n RCata)
      :+: Follow cont
