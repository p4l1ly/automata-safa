{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Afa.IORef where

import Afa.Finalful
import Afa.Finalful.STerm as STerm
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State (StateT (runStateT), get, put)
import Data.Functor ((<&>))
import qualified Data.HashMap.Strict as HM
import Data.IORef
import Lift
import qualified Shaper
import System.Mem.StableName
import TypeDict

type FR f = f (Ref f)
type R f = IORef (FR f)
type SN f = StableName (R f)
type S f = (SN f, R f)
data Ref f = Ref (S f) | Subtree (FR f)
data Anyrec
data Funrec
data Build
data BuildTree
data ShareTree
data Deref

-- Anyrec

type AnyTEnv f a m = (IORef (HM.HashMap (StableName (R f)) a), FR f -> AnyT f a m a)
type AnyTReaderT f a m = ReaderT (AnyTEnv f a m)
newtype AnyT f a (m :: * -> *) x = AnyT (ReaderT (Ref f) (AnyTReaderT f a m m) x)
  deriving (Functor, Applicative, Monad) via ReaderT (Ref f) (AnyTReaderT f a m m)
instance MonadTrans (AnyT f a) where
  lift = AnyT . lift . lift

type instance Shaper.RecTrans (Shaper.RecK (Ref f) (FR f) a n Anyrec) = AnyT f

instance
  {-# OVERLAPPING #-}
  (Monad m, Shaper.MLift n m IO) =>
  Shaper.MonadFn ( 'K Zero (Shaper.MfnK (Ref f) a (Shaper.RecK (Ref f) (FR f) a n Anyrec))) (AnyT f a m)
  where
  monadfn r@(Ref (name, ioref)) = do
    (cacheIoref, recur) <- AnyT (lift ask)
    cache <- lift $ Shaper.mlift @n $ readIORef cacheIoref
    case HM.lookup name cache of
      Just a -> return a
      Nothing -> do
        f <- lift $ Shaper.mlift @n $ readIORef ioref
        let AnyT action = recur f
        a <- AnyT $ local (const r) action
        lift $ Shaper.mlift @n $ writeIORef cacheIoref (HM.insert name a cache)
        return a
  monadfn r@(Subtree f) = do
    (_, recur) <- AnyT (lift ask)
    let AnyT action = recur f
    AnyT $ local (const r) action

instance Monad m => Shaper.MonadFn ( 'K Zero (Shaper.MfnK () (Ref f) (Shaper.RecK (Ref f) ff a n Anyrec))) (AnyT f a m) where
  monadfn () = AnyT ask

instance Monad m => Shaper.MonadFn ( 'K Zero (Shaper.IsTree (Shaper.RecK (Ref f) ff a n Anyrec))) (AnyT f a m) where
  monadfn () = AnyT $ ask <&> \case Subtree _ -> True; _ -> False

instance (Monad m, Shaper.MLift n m IO) => Shaper.Recur0 ( 'K Zero (Shaper.RecK (Ref f) (f (Ref f)) a n Anyrec)) m where
  recur action = do
    cacheIoref <- Shaper.mlift @n (newIORef HM.empty)
    return \r -> do
      let AnyT reader =
            Shaper.monadfn
              @( 'K Zero (Shaper.MfnK (Ref f) a (Shaper.RecK (Ref f) (FR f) a n Anyrec)))
              r
      runReaderT (runReaderT reader r) (cacheIoref, action)

--- /Anyrec

instance Shaper.MonadFn ( 'K Zero (Shaper.MfnK (Ref f) (f (Ref f)) Deref)) IO where
  monadfn (Ref (_, ioref)) = liftIO $ readIORef ioref
  monadfn (Subtree f) = return f

instance Shaper.MonadFn ( 'K Zero (Shaper.MfnK (f (Ref f)) (Ref f) Build)) IO where
  monadfn f = do
    ioref <- liftIO $ newIORef f
    name <- liftIO $ makeStableName ioref
    return $ Ref (name, ioref)

instance Shaper.MonadFn ( 'K Zero (Shaper.MfnK (f (Ref f)) (Ref f) BuildTree)) IO where
  monadfn f = return $ Subtree f

instance Shaper.MonadFn ( 'K Zero (Shaper.MfnK (Ref f) (Ref f) ShareTree)) IO where
  monadfn (Subtree f) = Shaper.monadfn @(Shaper.Mk (Shaper.MfnK (f (Ref f)) (Ref f)) ( 'K Zero Build)) f
  monadfn r = return r

instance
  Shaper.FunRecur
    ( 'K
        n
        ( Shaper.FRecK
            (Ref (Term q v))
            (Ref (Term q' v'))
            (QVFun q v q' v')
            Funrec
        )
    )
    IO
  where
  funRecur (QVFun qfn vfn) = do
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
  (Monad m, Shaper.MLift n m IO) =>
  Shaper.FunRecur
    ( 'K
        n
        ( Shaper.FRecK
            (Ref (Term q v))
            (Ref (Term q v))
            (RTra m (Ref (Term q v)) (Ref (Term q v)))
            Funrec
        )
    )
    m
  where
  funRecur (RTra rfn) = do
    let mlift :: IO a -> m a
        mlift = Shaper.mlift @n

    old2new <- Shaper.mlift @n $ newIORef (HM.empty :: HM.HashMap (SN (Term q v)) (Ref (Term q v)))

    let convert (State q) = return (State q)
        convert (Var v) = return (Var v)
        convert (And a b) = And <$> (convert' a >>= rfn) <*> (convert' b >>= rfn)
        convert (Or a b) = Or <$> (convert' a >>= rfn) <*> (convert' b >>= rfn)
        convert (Not a) = Not <$> (convert' a >>= rfn)
        convert LTrue = pure LTrue
        convert LFalse = pure LFalse

        convert' :: Ref (Term q v) -> m (Ref (Term q v))
        convert' (Ref (name, ioref)) = do
          hmap <- mlift $ readIORef old2new
          case HM.lookup name hmap of
            Just r' -> return r'
            Nothing -> do
              f' <- mlift (readIORef ioref) >>= convert
              ioref' <- mlift $ newIORef f'
              name' <- mlift $ makeStableName ioref'
              let r' = Ref (name', ioref')
              mlift $ writeIORef old2new (HM.insert name r' hmap)
              return r'
        convert' (Subtree f) = Subtree <$> convert f

    return convert'

type IORefRemoveFinalsD q v r r' =
  Name "q" q
    :+: Name "v" v
    :+: Name "r" r
    :+: Name "r'" r'
    :+: Name "lock" (Wrap Anyrec)
    :+: Name "any" (Wrap Anyrec)
    :+: Name "funr" (Wrap Funrec)
    :+: Name "buildTree" (Wrap BuildTree)
    :+: Name "shareTree" (Wrap ShareTree)
    :+: Name "deref" (Wrap Deref)
    :+: Name "fun" STerm.OneshotFun
    :+: Name "tra" STerm.OneshotTra
    :+: End

removeFinals ::
  forall s q v r r' d result.
  ( r ~ Ref (Term q v)
  , r' ~ Ref (Term (SyncQs q) (SyncVar q v))
  , d ~ IORefRemoveFinalsD q v r r'
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO (r', (Int, Int -> SyncQs q, Int -> r', SyncQs q -> Int))
removeFinals = Afa.Finalful.removeFinals @d
