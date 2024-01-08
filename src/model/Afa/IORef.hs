{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
-- {-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.IORef where

import Afa.Term
import Control.Arrow
import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Function.Apply
import Data.Functor
import Data.Functor.Compose
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.IORef
import InversionOfControl.Lift
import InversionOfControl.LiftN
import qualified InversionOfControl.MapRecur as MR
import InversionOfControl.MonadFn
import qualified InversionOfControl.Recur as R
import InversionOfControl.TypeDict
import System.Mem.StableName
import qualified Data.HashSet as HS
import System.Random
import System.IO.Unsafe
import Afa.ShallowHashable

type FR f = f (Ref f)
type R f = IORef (FR f)
type SN f = StableName (R f)
type S f = (SN f, R f)
data Ref f = Ref !(S f) | Subtree !(FR f)

instance ShallowEq (Ref f) where
  Ref (sn1, _) `shallowEq` Ref (sn2, _) = sn1 == sn2
  _ `shallowEq` _ = False

instance ShallowHashable (Ref f) where
  shallowHash salt (Ref (sn, _)) = hashWithSalt salt sn
  shallowHash salt (Subtree x) = unsafePerformIO randomIO

instance Eq (f (Ref f)) => Eq (Ref f) where
  Ref (sn1, _) == Ref (sn2, _) = sn1 == sn2
  Subtree fr1 == Subtree fr2 = fr1 == fr2
  _ == _ = False

instance Hashable (f (Ref f)) => Hashable (Ref f) where
  hashWithSalt salt (Ref (sn, _)) = hashWithSalt salt (False, sn)
  hashWithSalt salt (Subtree x) = hashWithSalt salt (True, x)

data Build
data Share
data Deref
data IsTree
data Replace
data Cata
data RCata
data PCata
data Hylo
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

replace :: Ref f -> FR f -> IO (Ref f)
replace (Subtree f) val = return $ Subtree val
replace ref@(Ref (_, ioref)) val = do
  writeIORef ioref val
  return ref

getSharingDetector :: (Traversable f, Hashable (FR f)) => IO (Ref f -> IO (Ref f))
getSharingDetector = do
  visitedVar <- newIORef HM.empty
  dbVar <- newIORef HM.empty
  let go fr = do
        fr1 <- traverse rec fr
        db <- readIORef dbVar
        (r', db') <-
          getCompose $
            HM.alterF -$ fr1 -$ db $
              Compose . \case
                Nothing -> shareTree fr1 <&> (id &&& Just)
                Just r' -> return (r', Just r')
        writeIORef dbVar db'
        return r'
      rec (Subtree fr) = go fr
      rec (Ref (name, ioref)) = do
        visited <- readIORef visitedVar
        case visited HM.!? name of
          Nothing -> do
            r' <- readIORef ioref >>= go
            modifyIORef' visitedVar $ HM.insert name r'
            return r'
          Just r' -> return r'
  return rec

-- The API calls for an applicative functor but the effort is not worth it yet.
getUnsharingDetector ::
  Traversable f =>
  (FR f -> Bool) ->
  IO (Ref f -> IO (), IO (Ref f -> IO (Ref f)))
getUnsharingDetector isShareable = do
  visitedVar <- newIORef HS.empty
  countsVar <- newIORef HM.empty
  let rec (Ref (name, ioref)) = do
        fr1 <- readIORef ioref
        visited <- readIORef visitedVar
        if HS.member name visited
          then return ()
          else do
            writeIORef visitedVar (HS.insert name visited)
            counts <- readIORef countsVar
            let counts' = foldr (\(Ref (k, _)) -> HM.insertWith (+) k 1) counts fr1
            writeIORef countsVar counts'
            mapM_ rec fr1

      countUp r@(Ref (name, _)) = do
        modifyIORef countsVar (HM.insertWith (+) name 1)
        rec r

  let finalize = do
        counts <- readIORef countsVar
        visitedVar <- newIORef HM.empty
        let go name fr = do
              fr1 <- traverse rec fr
              if isShareable fr1 && counts HM.! name > 1
                then shareTree fr1
                else return (Subtree fr1)
            rec (Ref (name, ioref)) = do
              visited <- readIORef visitedVar
              case HM.lookup name visited of
                Nothing -> do
                  fr <- readIORef ioref
                  r' <- go name fr
                  modifyIORef visitedVar (HM.insert name r')
                  return r'
                Just r' -> return r'
        return rec
  return (countUp, finalize)

instance MonadFn0 (Explicit (Ref f) Bool IsTree) IO where
  monadfn0 = return . isTree

instance MonadFn0 (Explicit (Ref f) (FR f) Deref) IO where
  monadfn0 = deref

instance MonadFn0 (Explicit (FR f) (Ref f) Build) IO where
  monadfn0 = return . Subtree

instance MonadFn0 (Explicit (Ref f) (Ref f) Share) IO where
  monadfn0 = share

instance MonadFn0 (Explicit (Ref f, FR f) (Ref f) Replace) IO where
  monadfn0 = uncurry replace


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
  (Monad m, LiftN n IO m, Hashable p) =>
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
              case HM.lookup (p, name) cache of
                Just b -> return b
                Nothing -> do
                  f <- liftIO' $ readIORef ioref
                  result <- getAlgebra recur (p, f)
                  liftIO' $ modifyIORef' cacheRef (HM.insert (p, name) result)
                  return result
    runIdentityT $ getAction recur

type instance R.Et (R.Explicit ('K _ Hylo) _ _ _) = R.BeforeAfter
instance
  (Monad m, LiftN n IO m, Monoid p) =>
  R.HyloRecur (R.Explicit ('K n Hylo) n' (Ref f) (FR f)) b p m
  where
  runHyloRecur = runHyloRecur1 @n

runHyloRecur1 ::
  forall (n :: Pean) a f m p b.
  (Monad m, LiftN n IO m, Monoid p) =>
  ((Ref f -> m ()) -> FR f -> m ()) ->
  ((Ref f -> p -> R.BeforeAfter m b) -> FR f -> p -> R.BeforeAfter m b) ->
  ((Ref f -> m ()) -> m ()) ->
  ((Ref f -> p -> R.BeforeAfter m b) -> R.BeforeAfter m a) ->
  m a
runHyloRecur1 getMarker getAlgebra getMarkingAction getAction = do
  countsRef <- liftn @n $ newIORef HM.empty

  let recurCount :: Ref f -> m ()
      recurCount r = do
        case r of
          Subtree f -> getMarker recurCount f
          Ref (name, ioref) -> do
            counts <- liftn @n $ readIORef countsRef
            case HM.lookup name counts of
              Just (count :: Int) ->
                liftn @n $ writeIORef countsRef $ HM.insert name (count + 1) counts
              Nothing -> do
                f <- liftn @n $ readIORef ioref
                liftn @n $ writeIORef countsRef $ HM.insert name 1 counts
                getMarker recurCount f

  topdownsRef <- liftn @n $ newIORef HM.empty
  algebrasRef <- liftn @n $ newIORef HM.empty
  resultsRef <- liftn @n $ newIORef HM.empty

  let recur :: Ref f -> p -> R.BeforeAfter m b
      recur (Subtree f) p = getAlgebra recur f p
      recur (Ref (name, ioref)) p = R.BeforeAfter do
        counts <- liftn @n (readIORef countsRef)

        case HM.lookup name counts of
          Nothing -> error "not marked"
          Just 0 -> error "too few marks"
          Just count -> do
            let count' = count - 1
            liftn @n $ writeIORef countsRef $ HM.insert name count' counts

            topdowns <- liftn @n $ readIORef topdownsRef
            p' <- case HM.lookup name topdowns of
              Nothing -> do
                liftn @n $ writeIORef topdownsRef $ HM.insert name p topdowns
                return p
              Just p0 -> do
                let p' = p0 <> p
                liftn @n $ writeIORef topdownsRef $ HM.insert name p' topdowns
                return p'

            when (count' == 0) do
              f <- liftn @n $ readIORef ioref
              let R.BeforeAfter runCoalgebra = getAlgebra recur f p'
              result <- runCoalgebra
              liftn @n $ modifyIORef algebrasRef $ HM.insert name result

            return do
              results <- liftn @n $ readIORef resultsRef
              case HM.lookup name results of
                Just b -> return b
                Nothing -> do
                  algebras <- liftn @n $ readIORef algebrasRef
                  case HM.lookup name algebras of
                    Nothing -> error "too many marks"
                    Just algebra -> do
                      result <- algebra
                      liftn @n $ modifyIORef' resultsRef $ HM.insert name result
                      return result

  getMarkingAction recurCount
  R.runBeforeAfter $ getAction recur

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

instance
  (Monad m, LiftN n IO m) =>
  MR.Recur (MR.Explicit ('K n MapRec) (Ref (Term q v)) (Ref (Term q' v')) (QVFun q v q' v')) m
  where
  runRecur (QVFun qfun vfun) = do
    R.runRecur
      @(R.Explicit ('K n RCata) Zero (Ref (Term q v)) (Ref (Term q v), Term q v (Ref (Term q v))))
      \rec (r, fr) -> do
        fr' <- case fr of
          LTrue -> return LTrue
          LFalse -> return LFalse
          State q -> return $ State (qfun q)
          Var v -> return $ Var (vfun v)
          Not r -> Not <$> rec r
          And r1 r2 -> And <$> rec r1 <*> rec r2
          Or r1 r2 -> Or <$> rec r1 <*> rec r2
        if isTree r
          then return $ Subtree fr'
          else lift $ liftn @n $ shareTree fr'

instance
  (Monad m, LiftN n IO m) =>
  MR.Recur
    ( MR.Explicit
        ('K n MapRec)
        (Ref (Term q v))
        (Ref (Term q v))
        (RTra m (Ref (Term q v)) (Ref (Term q v)))
    )
    m
  where
  runRecur (RTra rtra) = do
    R.runRecur
      @(R.Explicit ('K n RCata) Zero (Ref (Term q v)) (Ref (Term q v), Term q v (Ref (Term q v))))
      \rec (r, fr) -> do
        fr' <- case fr of
          LTrue -> return LTrue
          LFalse -> return LFalse
          State q -> return $ State q
          Var v -> return $ Var v
          Not r -> Not <$> rec r
          And r1 r2 -> And <$> rec r1 <*> rec r2
          Or r1 r2 -> Or <$> rec r1 <*> rec r2
        r' <-
          if isTree r
            then return $ Subtree fr'
            else lift $ liftn @n $ shareTree fr'
        lift $ rtra r'

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
      :+: Name "replace" Replace
      :+: Name "cata" Cata
      :+: Name "rcata" RCata
      :+: Name "pcata" PCata
      :+: Name "hylo" Hylo
      :+: Name "mapRec" MapRec
      :+: Name "mapRecCopy" MapRec
      :+: Name "mapRecFun" OneshotFun
      :+: Name "mapRecFunCopy" OneshotFun
      :+: Name "mapRecTra" OneshotTra
      :+: Name "mapRecFunR'" FunR'
      :+: Follow cont
