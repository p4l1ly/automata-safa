{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Afa.STRef where

import Afa.Finalful
import Afa.Finalful.STerm as STerm
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State (StateT (runStateT), get, put)
import qualified Data.HashMap.Strict as HM
import Data.IORef
import Data.STRef
import qualified Shaper
import System.Mem.StableName
import TypeDict

type FR f = f (Ref f)
type R f = IORef (FR f)
type SN f = StableName (R f)
type S f = (SN f, R f)
data Ref f = Ref (S f) | Subtree (FR f) -- TODO heterogeneous recursion => no subtree needed, use Free (but there are no real benefits in this case)
data Anyrec
data Funrec
data Build
data Deref

-- Anyrec

type AnyTEnv f a m = (IORef (HM.HashMap (StableName (R f)) a), FR f -> AnyT f a m a)
type AnyTReaderT f a m = ReaderT (AnyTEnv f a m)
newtype AnyT f a (m :: * -> *) x = AnyT (ReaderT (Ref f) (AnyTReaderT f a m m) x)
  deriving (Functor, Applicative, Monad) via ReaderT (Ref f) (AnyTReaderT f a m m)
instance MonadTrans (AnyT f a) where
  lift = AnyT . lift . lift

type instance Shaper.RecTrans (Shaper.RecK Anyrec (Ref f) (FR f) a) = AnyT f

instance
  MonadIO m =>
  Shaper.MonadFn (Shaper.MfnK (Shaper.RecK Anyrec (Ref f) (FR f) a) (Ref f) a) (AnyT f a m)
  where
  monadfn r@(Ref (name, ioref)) = do
    (cacheIoref, recur) <- AnyT (lift ask)
    cache <- lift $ liftIO $ readIORef cacheIoref
    case HM.lookup name cache of
      Just a -> return a
      Nothing -> do
        f <- lift $ liftIO $ readIORef ioref
        let AnyT action = recur f
        a <- AnyT $ local (const r) action
        lift $ liftIO $ writeIORef cacheIoref (HM.insert name a cache)
        return a
  monadfn r@(Subtree f) = do
    (_, recur) <- AnyT (lift ask)
    let AnyT action = recur f
    AnyT $ local (const r) action

instance
  (r ~ Ref f, Monad m) =>
  Shaper.MonadFn (Shaper.MfnK (Shaper.RecK Anyrec (Ref f) (FR f) a) () r) (AnyT f a m)
  where
  monadfn () = AnyT ask

instance MonadIO m => Shaper.Recur (Shaper.RecK Anyrec (Ref f) (f (Ref f)) a) m where
  recur action r = do
    cacheIoref <- liftIO $ newIORef HM.empty
    let AnyT reader =
          Shaper.monadfn
            @(Shaper.MfnK (Shaper.RecK Anyrec (Ref f) (f (Ref f)) a) (Ref f) a)
            r
    runReaderT (runReaderT reader r) (cacheIoref, action)

--- /Anyrec

instance MonadIO m => Shaper.MonadFn (Shaper.MfnK Deref (Ref f) (f (Ref f))) m where
  monadfn (Ref (_, ioref)) = liftIO $ readIORef ioref
  monadfn (Subtree f) = return f

-- TODO heterogeneous recursion would allow interleaving trees and dags
instance MonadIO m => Shaper.MonadFn (Shaper.MfnK Build (f (Ref f)) (Ref f)) m where
  monadfn f = do
    ioref <- liftIO $ newIORef f
    name <- liftIO $ makeStableName ioref
    return $ Ref (name, ioref)

instance
  Shaper.FunRecur
    ( Shaper.FRecK
        Funrec
        (Ref (Term q v))
        (Ref (Term q' v'))
        (PerVarMFun (q' `Q` v' `V` E q v r))
    )
    IO
  where
  funRecur (PerVarMFun qfn vfn _) = do
    old2new <- newIORef (HM.empty :: HM.HashMap (SN (Term q v)) (Ref (Term q' v')))

    let convert (State q) = return (State (qfn q))
        convert (Var v) = return (Var (vfn v))
        convert (And a b) = And <$> convert' a <*> convert' b
        convert (Or a b) = Or <$> convert' a <*> convert' b
        convert (Not a) = Not <$> convert' a
        convert LTrue = pure LTrue
        convert LFalse = pure LFalse

        convert' :: Ref (Term q v) -> IO (Ref (Term q' v'))
        convert' (Ref (name, ioref)) = do
          hmap <- readIORef old2new
          case HM.lookup name hmap of
            Just r' -> return r'
            Nothing -> do
              f' <- readIORef ioref >>= convert
              ioref' <- newIORef f'
              name' <- makeStableName ioref'
              let r' = Ref (name', ioref')
              writeIORef old2new (HM.insert name r' hmap)
              return r'
        convert' (Subtree f) = Subtree <$> convert f

    return convert'

instance
  Shaper.FunRecur
    ( Shaper.FRecK
        Funrec
        (Ref (Term q v))
        (Ref (Term q v))
        (PerVarMTra ( 'MTra (Ref (Term q v) `STerm.R` E q v (Ref (Term q v))) IO))
    )
    IO
  where
  funRecur (PerVarMTra _ _ rfn) = do
    old2new <- newIORef (HM.empty :: HM.HashMap (SN (Term q v)) (Ref (Term q v)))

    let convert (State q) = return (State q)
        convert (Var v) = return (Var v)
        convert (And a b) = And <$> rfn a <*> rfn b
        convert (Or a b) = Or <$> rfn a <*> rfn b
        convert (Not a) = Not <$> rfn a
        convert LTrue = pure LTrue
        convert LFalse = pure LFalse

        convert' :: Ref (Term q v) -> IO (Ref (Term q v))
        convert' (Ref (name, ioref)) = do
          hmap <- readIORef old2new
          case HM.lookup name hmap of
            Just r' -> return r'
            Nothing -> do
              f' <- readIORef ioref >>= convert
              ioref' <- newIORef f'
              name' <- makeStableName ioref'
              let r' = Ref (name', ioref')
              writeIORef old2new (HM.insert name r' hmap)
              return r'
        convert' (Subtree f) = Subtree <$> convert f

    return convert'

removeFinals ::
  forall s q v r r' d result.
  ( r ~ Ref (Term q v)
  , r' ~ Ref (Term (SyncQs q) (SyncVar q v))
  , d
      ~ ( Name "q" q
            :+: Name "v" v
            :+: Name "r" r
            :+: Name "r'" r'
            :+: Name "lock" Anyrec
            :+: Name "any" Anyrec
            :+: Name "funr" Funrec
            :+: Name "build" Build
            :+: Name "deref" Deref
            :+: Name "fun" PerVarMFun
            :+: Name "tra" PerVarMTra
            :+: End
        )
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO (r', (Int, Int -> SyncQs q, Int -> r', SyncQs q -> Int))
removeFinals = Afa.Finalful.removeFinals @d
