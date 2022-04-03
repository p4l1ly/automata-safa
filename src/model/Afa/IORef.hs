{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.IORef where

import qualified Afa.DnfStates as QDnf
import Afa.Finalful
import Afa.Finalful.STerm as STerm
import Afa.Negate (Qombo)
import qualified Afa.Negate as Negate
import qualified Afa.Separated as Separ
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State (StateT (runStateT), get, put)
import Data.Array
import Data.Foldable (toList)
import Data.Function.Apply ((-$))
import Data.Functor (($>), (<&>))
import Data.Functor.Compose (Compose (Compose, getCompose))
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.IORef
import Data.Monoid (Endo (appEndo))
import qualified Data.Text as T
import Data.Traversable (for)
import Lift
import Shaper (FRecK, FunRecur, IsTree, MLift (mlift), MfnK, Mk, MkN, MonadFn (monadfn), RecK, RecTrans, Recur0 (recur))
import qualified Shaper
import Shaper.Helpers (buildFree)
import System.IO
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

type instance RecTrans (RecK (Ref f) (FR f) a n Anyrec) = AnyT f

instance
  {-# OVERLAPPING #-}
  (Monad m, MLift n m IO) =>
  MonadFn ( 'K Zero (MfnK (Ref f) a (RecK (Ref f) (FR f) a n Anyrec))) (AnyT f a m)
  where
  monadfn r@(Ref (name, ioref)) = do
    (cacheIoref, recur) <- AnyT (lift ask)
    cache <- lift $ mlift @n $ readIORef cacheIoref
    case HM.lookup name cache of
      Just a -> return a
      Nothing -> do
        f <- lift $ mlift @n $ readIORef ioref
        let AnyT action = recur f
        a <- AnyT $ local (const r) action
        lift $ mlift @n $ writeIORef cacheIoref (HM.insert name a cache)
        return a
  monadfn r@(Subtree f) = do
    (_, recur) <- AnyT (lift ask)
    let AnyT action = recur f
    AnyT $ local (const r) action

instance Monad m => MonadFn ( 'K Zero (MfnK () (Ref f) (RecK (Ref f) ff a n Anyrec))) (AnyT f a m) where
  monadfn () = AnyT ask

instance Monad m => MonadFn ( 'K Zero (IsTree (RecK (Ref f) ff a n Anyrec))) (AnyT f a m) where
  monadfn () = AnyT $ ask <&> \case Subtree _ -> True; _ -> False

instance (Monad m, MLift n m IO) => Recur0 ( 'K Zero (RecK (Ref f) (f (Ref f)) a n Anyrec)) m where
  recur action = do
    cacheIoref <- mlift @n (newIORef HM.empty)
    return \r -> do
      let AnyT reader =
            monadfn
              @( 'K Zero (MfnK (Ref f) a (RecK (Ref f) (FR f) a n Anyrec)))
              r
      runReaderT (runReaderT reader r) (cacheIoref, action)

--- /Anyrec

instance MonadFn ( 'K Zero (MfnK (Ref f) (f (Ref f)) Deref)) IO where
  monadfn (Ref (_, ioref)) = liftIO $ readIORef ioref
  monadfn (Subtree f) = return f

instance MonadFn ( 'K Zero (MfnK (f (Ref f)) (Ref f) Build)) IO where
  monadfn f = do
    ioref <- liftIO $ newIORef f
    name <- liftIO $ makeStableName ioref
    return $ Ref (name, ioref)

instance MonadFn ( 'K Zero (MfnK (f (Ref f)) (Ref f) BuildTree)) IO where
  monadfn f = return $ Subtree f

instance MonadFn ( 'K Zero (MfnK (Ref f) (Ref f) ShareTree)) IO where
  monadfn (Subtree f) = monadfn @(Mk (MfnK (f (Ref f)) (Ref f)) ( 'K Zero Build)) f
  monadfn r = return r

instance
  FunRecur
    ( 'K
        n
        ( FRecK
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
  FunRecur
    ( 'K
        n
        ( FRecK
            (Ref (Term q v))
            (Ref (Term q' v))
            (QFun q q')
            Funrec
        )
    )
    IO
  where
  funRecur (QFun qfn) = do
    old2new <- newIORef (HM.empty :: HM.HashMap (SN (Term q v)) (Ref (Term q' v')))

    let convert (State q) = return (State (qfn q))
        convert (Var v) = return (Var v)
        convert (And a b) = And <$> convert' a <*> convert' b
        convert (Or a b) = Or <$> convert' a <*> convert' b
        convert (Not a) = Not <$> convert' a
        convert LTrue = pure LTrue
        convert LFalse = pure LFalse

        convert' :: Ref (Term q v) -> IO (Ref (Term q' v))
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
  (Monad m, MLift n m IO) =>
  FunRecur
    ( 'K
        n
        ( FRecK
            (Ref (Term q v))
            (Ref (Term q v))
            (RTra m (Ref (Term q v)) (Ref (Term q v)))
            Funrec
        )
    )
    m
  where
  funRecur (RTra rfn) = do
    let my_mlift :: IO a -> m a
        my_mlift = mlift @n

    old2new <- mlift @n $ newIORef (HM.empty :: HM.HashMap (SN (Term q v)) (Ref (Term q v)))

    let convert (State q) = return (State q)
        convert (Var v) = return (Var v)
        convert (And a b) = And <$> (convert' a >>= rfn) <*> (convert' b >>= rfn)
        convert (Or a b) = Or <$> (convert' a >>= rfn) <*> (convert' b >>= rfn)
        convert (Not a) = Not <$> (convert' a >>= rfn)
        convert LTrue = pure LTrue
        convert LFalse = pure LFalse

        convert' :: Ref (Term q v) -> m (Ref (Term q v))
        convert' (Ref (name, ioref)) = do
          hmap <- my_mlift $ readIORef old2new
          case HM.lookup name hmap of
            Just r' -> return r'
            Nothing -> do
              f' <- my_mlift (readIORef ioref) >>= convert
              ioref' <- my_mlift $ newIORef f'
              name' <- my_mlift $ makeStableName ioref'
              let r' = Ref (name', ioref')
              my_mlift $ writeIORef old2new (HM.insert name r' hmap)
              return r'
        convert' (Subtree f) = Subtree <$> convert f

    return convert'

instance
  (Monad m, MLift n m IO) =>
  FunRecur
    ( 'K
        n
        ( FRecK
            (Ref (Term q v))
            (Ref (Term q v'))
            (VarTra m v q v' (Ref (Term q v')))
            Funrec
        )
    )
    m
  where
  funRecur (VarTra vfn) = do
    let my_mlift :: IO a -> m a
        my_mlift = mlift @n

    old2new <- mlift @n $ newIORef (HM.empty :: HM.HashMap (SN (Term q v)) (Ref (Term q v')))

    let convert (State q) = return (State q)
        convert (Var v) = vfn v
        convert (And a b) = And <$> convert' a <*> convert' b
        convert (Or a b) = Or <$> convert' a <*> convert' b
        convert (Not a) = Not <$> convert' a
        convert LTrue = pure LTrue
        convert LFalse = pure LFalse

        convert' :: Ref (Term q v) -> m (Ref (Term q v'))
        convert' (Ref (name, ioref)) = do
          hmap <- my_mlift $ readIORef old2new
          case HM.lookup name hmap of
            Just r' -> return r'
            Nothing -> do
              f' <- my_mlift (readIORef ioref) >>= convert
              ioref' <- my_mlift $ newIORef f'
              name' <- my_mlift $ makeStableName ioref'
              let r' = Ref (name', ioref')
              my_mlift $ writeIORef old2new (HM.insert name r' hmap)
              return r'
        convert' (Subtree f) = Subtree <$> convert f

    return convert'

data Delit (xBuild :: *) (xDeref :: *)
type DelitKBuild q v r x = 'K Zero (MfnK (Term q v r) r x)
type DelitKDeref q v r x = 'K Zero (MfnK r (Term q v r) x)

instance
  ( MonadFn (DelitKBuild q v r xBuild) m
  , MonadFn (DelitKDeref q v r xDeref) m
  ) =>
  MonadFn ( 'K Zero (MfnK (Term q v r) r (Delit xBuild xDeref))) m
  where
  monadfn = \case
    fr@(Not r) -> deref r >>= build . \case LTrue -> LFalse; LFalse -> LTrue; _ -> fr
    fr@(And a b) ->
      deref a >>= \case
        LTrue -> return b
        LFalse -> build LFalse
        _ ->
          deref b >>= \case
            LTrue -> return a
            LFalse -> build LFalse
            _ -> build fr
    fr@(Or a b) ->
      deref a >>= \case
        LFalse -> return b
        LTrue -> build LTrue
        _ ->
          deref b >>= \case
            LFalse -> return a
            LTrue -> build LTrue
            _ -> build fr
    fr -> build fr
    where
      deref = monadfn @(DelitKDeref q v r xDeref)
      build = monadfn @(DelitKBuild q v r xBuild)

type IORefRemoveFinalsD q v r r' =
  Name "q" q
    :+: Name "v" v
    :+: Name "r" r
    :+: Name "r'" r'
    :+: Name "lock" (Wrap Anyrec)
    :+: Name "any" (Wrap Anyrec)
    :+: Name "funr" (Wrap Funrec)
    :+: Name "buildTree" (Wrap (Delit BuildTree Deref))
    :+: Name "shareTree" (Wrap ShareTree)
    :+: Name "deref" (Wrap Deref)
    :+: Name "fun" STerm.OneshotFun
    :+: Name "tra" STerm.OneshotTra
    :+: End

removeFinals ::
  forall q v r r' d.
  ( r ~ Ref (Term q v)
  , r' ~ Ref (Term (SyncQs q) (SyncVar q v))
  , d ~ IORefRemoveFinalsD q v r r'
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO (r', (Int, Int -> SyncQs q, Int -> r', SyncQs q -> Int))
removeFinals = Afa.Finalful.removeFinals @d

data Fail
instance Monad m => MonadFn ( 'K Zero (MfnK e a Fail)) (ExceptT e m) where
  monadfn = throwError

-- this could be more generic and reside in Afa.Separated
trySeparateQTransitions ::
  forall q v r r' d sepF d' buildTree.
  ( r ~ Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , sepF ~ MkN (RecK r (Term q v r) (Separ.AQ r)) (Inc [d|lock|])
  , d' ~ (Name "fail" ( 'K (Succ Zero) Fail) :+: Name "rec" sepF :+: LiftTags (LiftTags d))
  , buildTree ~ Mk (MfnK (Term q v r) r) [d|buildTree|]
  , Show q
  , Show v
  ) =>
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO (Maybe (Int, Int -> q, Int -> [(r, r)], q -> Int))
trySeparateQTransitions (qCount, i2q, i2r, q2i) = do
  rTrue <- monadfn @buildTree LTrue
  result <- runExceptT $ do
    separ <- recur @sepF (Separ.trySeparateAlg @d')
    i2r' <-
      listArray (0, qCount - 1) <$> for [0 .. qCount - 1] \(i2r -> r) ->
        separ r <&> \case
          Separ.A ref -> [(ref, rTrue)]
          Separ.Q ref -> [(rTrue, ref)]
          Separ.AQAnd ref ref' -> [(ref, ref')]
          Separ.AQOr aq1s ->
            aq1s <&> \case
              Separ.A1 ref -> (ref, rTrue)
              Separ.Q1 ref -> (rTrue, ref)
              Separ.AQAnd1 ref ref' -> (ref, ref')
    return (qCount, i2q, (i2r' !), q2i)

  case result of
    Left (term :: Term q v (Separ.AQ r)) -> do
      let term' = getCompose $ Compose term $> ()
      hPutStrLn stderr ("Error: " ++ show term') $> Nothing
    Right x -> return (Just x)

-- this could be more generic and reside in Afa.Separated
boomSeparateQTransitions ::
  forall q v r r' d sepF d' buildTree.
  ( r ~ Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , sepF ~ MkN (RecK r (Term q v r) (Separ.AQ r)) [d|lock|]
  , d' ~ (Name "rec" sepF :+: LiftTags d)
  , buildTree ~ Mk (MfnK (Term q v r) r) [d|buildTree|]
  , Show q
  , Show v
  ) =>
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO (Int, Int -> q, Int -> [(r, r)], q -> Int)
boomSeparateQTransitions (qCount, i2q, i2r, q2i) = do
  rTrue <- monadfn @buildTree LTrue
  separ <- recur @sepF (Separ.boomSeparateAlg @d')
  i2r' <-
    listArray (0, qCount - 1) <$> for [0 .. qCount - 1] \(i2r -> r) ->
      separ r <&> \case
        Separ.A ref -> [(ref, rTrue)]
        Separ.Q ref -> [(rTrue, ref)]
        Separ.AQAnd ref ref' -> [(ref, ref')]
        Separ.AQOr aq1s ->
          aq1s <&> \case
            Separ.A1 ref -> (ref, rTrue)
            Separ.Q1 ref -> (rTrue, ref)
            Separ.AQAnd1 ref ref' -> (ref, ref')
  return (qCount, i2q, (i2r' !), q2i)

removeFinalsHind ::
  forall q v r r' d.
  ( r ~ Ref (Term q v)
  , r' ~ Ref (Term (SyncQs q) (SyncVar q v))
  , d ~ IORefRemoveFinalsD q v r r'
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> [(r, r)], q -> Int) ->
  IO (r', (Int, Int -> SyncQs q, Int -> [(r', r')], SyncQs q -> Int))
removeFinalsHind = Afa.Finalful.removeFinalsHind @d

unseparateQTransitions ::
  forall q v r r' d buildTree buildD f.
  ( r ~ Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , buildTree ~ Mk (MfnK (Term q v r) r) [d|buildTree|]
  , buildD ~ (Name "build" buildTree :+: d)
  , Foldable f
  ) =>
  (Int, Int -> q, Int -> f (r, r), q -> Int) ->
  IO (Int, Int -> q, Int -> r, q -> Int)
unseparateQTransitions (qCount, i2q, i2r, q2i) = do
  rFalse <- monadfn @buildTree LFalse
  rs <- for [0 .. qCount - 1] \(i2r -> ts) -> do
    foldM -$ rFalse -$ ts $ \result (a, q) -> do
      buildFree @buildD (Free $ Or (Pure result) (Free $ And (Pure a) (Pure q)))
  let qrmap = listArray (0, qCount - 1) rs
  return (qCount, i2q, (qrmap !), q2i)

-- this could be more generic and reside in Afa.Separated
toQDnf ::
  forall q v r r' d recK d' buildTree shareTree.
  ( r ~ Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , recK ~ MkN (RecK r (Term q v r) [r]) [d|lock|]
  , buildTree ~ Mk (MfnK (Term q v r) r) [d|buildTree|]
  , shareTree ~ Mk (MfnK r r) [d|shareTree|]
  , d' ~ (Name "rec" recK :+: LiftTags d)
  ) =>
  (Int, Int -> q, Int -> [(r, r)], q -> Int) ->
  IO (Int, Int -> q, Int -> [(r, r)], q -> Int)
toQDnf (qCount, i2q, i2r, q2i) = do
  rFalse <- monadfn @buildTree LFalse
  qdnf <- recur @recK (QDnf.qdnfAlg @d')
  i2r' <-
    listArray (0, qCount - 1)
      <$> for [0 .. qCount - 1] \(i2r -> aqs) ->
        concat <$> for aqs \(a, q) ->
          qdnf q >>= \case
            [q] -> return [(a, q)]
            qs -> do
              a' <- monadfn @shareTree a
              return $ map (a',) qs
  return (qCount, i2q, (i2r' !), q2i)

-- this could be more generic and reside in Negate.deMorganAlg
negateSeparated ::
  forall q v r r' d morgF d' buildTree f.
  ( r ~ Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , morgF ~ MkN (RecK r (Term q v r) r) [d|lock|]
  , d' ~ (Name "rec" morgF :+: LiftTags d)
  , buildTree ~ Mk (MfnK (Term q v r) r) [d|buildTree|]
  , Foldable f
  ) =>
  r ->
  f q ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO (r, [q], (Int, Int -> q, Int -> r, q -> Int))
negateSeparated init finals (qCount, i2q, i2r, q2i) = do
  deMorgan <- recur @morgF (Negate.deMorganAlg @d')
  init' <- deMorgan init
  let nonfinals =
        accumArray (\_ _ -> False) True (0, qCount - 1) $
          map ((,()) . q2i) $ toList finals
  let finals' = map i2q $ filter (nonfinals !) [0 .. qCount - 1]
  qts' <- for [0 .. qCount - 1] $ deMorgan . i2r
  let qts'Arr = listArray (0, qCount - 1) qts'
  return (init', finals', (qCount, i2q, (qts'Arr !), q2i))

-- this could be more generic and reside in Negate.deMorganAlg
qombo ::
  forall q v r r' d f fq.
  ( r ~ Ref (Term q v)
  , r' ~ Ref (Term (Qombo q) v)
  , d ~ IORefRemoveFinalsD q v r r'
  , Foldable f
  ) =>
  [(r, f q, (Int, Int -> q, Int -> r, q -> Int))] ->
  IO ([r'], [Qombo q], (Int, Int -> Qombo q, Int -> r', Qombo q -> Int))
qombo = Negate.qombo @d

-- this could be more generic and reside in Negate.deMorganAlg
splitFinals ::
  forall q v r d d' splitF buildTree shareTree deref.
  ( r ~ Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r
  , splitF ~ MkN (RecK r (Term q v r) (SplitFinalsR r q)) [d|lock|]
  , d'
      ~ ( Name "rec" splitF
            :+: LiftTags
                  ( Name "buildTree" (Mk (MfnK (Term q v r) r) [d|buildTree|])
                      :+: Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
                      :+: Name "deref" (Mk (MfnK r (Term q v r)) [d|deref|])
                      :+: d
                  )
        )
  ) =>
  r ->
  IO ([q], Maybe r)
splitFinals final = do
  splitF <- recur @splitF (Afa.Finalful.splitFinals @d')
  ((_, (`appEndo` []) -> nonfinals), complex) <- splitF final
  return (nonfinals, complex)
