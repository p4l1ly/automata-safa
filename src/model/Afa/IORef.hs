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
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.IORef where

import Afa.Term
import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Function.Apply
import qualified Data.HashMap.Strict as HM
import Data.IORef
import InversionOfControl.Lift
import InversionOfControl.LiftN
import qualified InversionOfControl.MapRecur as MR
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
data PCata
data MapRec

isTree :: Ref f -> Bool
isTree (Ref _) = False
isTree (Subtree f) = True

deref :: Ref f -> IO (f (Ref f))
deref (Ref (_, ioref)) = readIORef ioref
deref (Subtree f) = return f

shareTree :: f (Ref f) -> IO (Ref f)
shareTree f = do
  ioref <- newIORef f
  name <- makeStableName ioref
  return $ Ref (name, ioref)

share :: Ref f -> IO (Ref f)
share (Subtree f) = shareTree f
share r = return r

instance MonadFn0 (Explicit (Ref f) Bool IsTree) IO where
  monadfn0 = return . isTree

instance MonadFn0 (Explicit (Ref f) (f (Ref f)) Deref) IO where
  monadfn0 = deref

instance MonadFn0 (Explicit (f (Ref f)) (Ref f) Build) IO where
  monadfn0 = return . Subtree

instance MonadFn0 (Explicit (Ref f) (Ref f) Share) IO where
  monadfn0 = share

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

type instance R.Et (R.Explicit ('K _ PCata) _ _ _) = IdentityT
instance
  (Monad m, LiftN n IO m) =>
  R.Recur (R.Explicit ('K n PCata) n' (p, Ref f) (p, FR f)) b m
  where
  runRecur getAlgebra getAction = do
    cacheRef <- liftn @n $ newIORef HM.empty
    let liftIO' :: IO a -> _ a
        liftIO' = liftn @n' @(IdentityT m) . lift . liftn @n
    let recur (p, r) = do
          case r of
            Subtree f -> getAlgebra recur (p, f)
            Ref (name, ioref) -> do
              cache <- liftIO' $ readIORef cacheRef
              case HM.lookup name cache of
                Just b -> return b
                Nothing -> do
                  f <- liftIO' $ readIORef ioref
                  result <- getAlgebra recur (p, f)
                  liftIO' $ modifyIORef' cacheRef (HM.insert name result)
                  return result
    runIdentityT $ getAction recur

type instance MR.Et (MR.Explicit ('K _ MapRec) _ _ _) = IdentityT
instance
  (Monad m, LiftN n IO m) =>
  MR.Recur (MR.Explicit ('K n MapRec) (Ref (Term q v)) (Ref (Term q' v)) (QFun q q')) m
  where
  runRecur (QFun qfun) = do
    R.runRecur
      @(R.Explicit ('K n RCata) Zero (Ref (Term q v)) (Ref (Term q v), Term q v (Ref (Term q v))))
      \rec (r, fr) -> do
        fr' <- case fr of
          LTrue -> return LTrue
          LFalse -> return LFalse
          State q -> return $ State (qfun q)
          Var v -> return $ Var v
          Not r -> Not <$> rec r
          And r1 r2 -> And <$> rec r1 <*> rec r2
          Or r1 r2 -> Or <$> rec r1 <*> rec r2
        if isTree r
          then return $ Subtree fr'
          else lift $ liftn @n $ shareTree fr'

data FunR' (r :: *) (mfun :: [QVR])
type instance
  Creation (FunR' r mfun) input =
    OneshotNext Ctx0 Ctx0 mfun (OneshotFunInput input (FunR'Selector r))
data FunR'Selector (r0 :: *) (inctx :: Ctx) (outctx :: Ctx)
type instance
  FunSelector (FunR'Selector r0 '(q, v, r) '(q', v', r')) =
    SelectorQ r0 q v r q' v' r'
type family SelectorQ r0 q v r q' v' r' where
  SelectorQ (Ref (Term q v0)) (Just q) v r (Just q') v' r' =
    SelectorV (Ref (Term q' v0)) v r v' r'
  SelectorQ r0 Nothing v r Nothing v' r' = SelectorV r0 v r v' r'
type family SelectorV r0 v r v' r' where
  SelectorV (Ref (Term q v)) (Just v) r (Just v') r' =
    SelectorR (Ref (Term q v')) r r'
  SelectorV r0 Nothing r Nothing r' = SelectorR r0 r r'
type family SelectorR r0 r r' where
  SelectorR (Ref (Term q v)) (Just (Ref (Term q v))) (Just (Ref (Term q' v'))) =
    Ref (Term q' v')
  SelectorR r Nothing Nothing = r

data IORefO (cont :: *)
type instance
  Definition (IORefO cont) =
    Name "build" Build
      :+: Name "share" Share
      :+: Name "deref" Deref
      :+: Name "isTree" IsTree
      :+: Name "cata" Cata
      :+: Name "rcata" RCata
      :+: Name "pcata" PCata
      :+: Name "mapRec" MapRec
      :+: Name "mapRecFun" OneshotFun
      :+: Name "mapRecFunR'" FunR'
      :+: Follow cont
