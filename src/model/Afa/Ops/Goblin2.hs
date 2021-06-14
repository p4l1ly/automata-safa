{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Afa.Ops.Goblin2 where

import Debug.Trace
import Data.String.Interpolate

import Control.Monad.Identity
import Data.Tuple
import Data.Bifunctor
import Data.Foldable
import Data.Array.Base (unsafeWrite, unsafeAt, unsafeAccumArray, numElements)
import GHC.Exts hiding (toList)
import Control.Monad.Free
import Data.Traversable
import Data.Array.ST
import Data.Array.Unsafe
import Data.Functor
import Control.Monad
import Data.Array
import Control.Monad.ST
import Control.Lens
import Control.Monad.Trans
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Void
import Data.Maybe
import Data.STRef
import Control.Monad.Reader (ReaderT(..))
import Capability.Reader
import Capability.State
import Capability.Source
import Capability.Sink
import GHC.Generics
import Data.Hashable
import Data.Coerce (coerce)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Control.RecursionSchemes.Lens
import qualified Control.RecursionSchemes.Utils.HashCons2 as QCons
import qualified Control.RecursionSchemes.Utils.HashCons3 as TCons
import qualified Control.RecursionSchemes.Utils.HashCons4 as InTCons
import Control.RecursionSchemes.Utils.HasIxed
import Control.RecursionSchemes.Utils.GrowableArray (GrowableArray(GrowableArray))
import qualified Control.RecursionSchemes.Utils.GrowableArray as GArray

import Afa.Lib (listArrayN)
import Afa.Lib.LiftArray
import Afa
import Afa.Term.Mix
import Afa.Term.Mix.Simplify (deUnary, canonicalizeWith)

-- {-# INLINABLE goblinUntilFixpoint #-}
-- goblinUntilFixpoint :: forall p. (Show p, Eq p) => AfaUnswallowed p -> AfaUnswallowed p
-- goblinUntilFixpoint afa = afa'{terms = unmarked} where
--   marked = markBack afa
--   closure afa = maybe afa (closure . removeUnused)$ goblin2 afa
--   afa' = closure$ afa{terms = marked}
--   unmarked = terms afa' <&> appMTFun mtfun0{mtfunQ = snd, mtfunT = snd}

data BackEdgeMark p
  = Unvisited
  | Recur
  | Recurring
  | Evaluated (Term p (Bool, Int) (Bool, Int))
  deriving Show

instance Semigroup (BackEdgeMark p) where
  Unvisited <> x = x
  x <> _ = x

goblinUntilFixpoint :: forall p. (Show p, Eq p, Hashable p) => AfaUnswallowed p -> AfaUnswallowed p
goblinUntilFixpoint afa = goblin2$ afa{terms = markBack afa}

{-# INLINABLE markBack #-}
markBack :: forall p. Show p => AfaUnswallowed p
  -> Array Int (Term p (Bool, Int) (Bool, Int))
markBack afa@(Afa terms states init) = runST getMarks &
  \arr -> listArray (bounds arr) (zip [0..] (elems arr)) <&>
    \case (_, Evaluated x) -> x; (i, _) -> error$ show (i, afa)
  where
  getMarks :: forall s. ST s (Array Int (BackEdgeMark p))
  getMarks = do
    marks <- newArray @(STArray s) (bounds terms) Unvisited
    unsafeWrite marks (states `unsafeAt` init) Recur
    dfs (traversal marks) marks (states `unsafeAt` init)
    unsafeFreeze marks

  traversal :: STArray s Int (BackEdgeMark p)
    -> LensLike (ST s) (BackEdgeMark p, Int) Bool (BackEdgeMark p, Int) Bool
  traversal arr rec (x, i) = case x of
    Recur -> do
      unsafeWrite arr i Recurring 
      term' <- terms `unsafeAt` i & modChilds pureChildMod
        { lQ = \q -> (, q) <$> rec (Recur, states `unsafeAt` q)
        , lT = \j -> (, j) <$> rec (Recur, j)
        }
      unsafeWrite arr i (Evaluated term')
      return False
    Recurring -> return True
    Evaluated _ -> return False
    Unvisited -> error "visiting unvisited"

data QRef = QRef
  Bool
  Int
  Int
  Bool
  deriving (Eq, Show)

data Mix
  = PureA (Bool, Int)
  | PureQ QRef
  | OrMix QRef (Bool, Int)
  | AndMix QRef (Bool, Int)
  deriving (Eq, Show)

type BackTerm' p = Term p (Bool, Int) (Bool, Int)
type Term' p = Term p Int Int
type InTConsState s p = InTCons.ConsState (LSTArray s) (BackTerm' p) (BackTerm' p)
type TConsState s p = TCons.ConsState (Term' p) (Term' p)

data BuilderCtx s p = BuilderCtx
  { qcons :: STRef s (QCons.ConsState Int Int)
  , inTcons :: STRef s (InTConsState s p)
  , tcons :: STRef s (TConsState s p)
  , algDomain :: STRef s (GrowableArray (LSTArray s) (Mix, Int))
  , wasNewQ :: STRef s Bool
  } deriving Generic
newtype Builder s p a = Builder { runBuilder :: BuilderCtx s p -> ST s a }
  deriving (Functor, Applicative, Monad) via (ReaderT (BuilderCtx s p) (ST s))
  deriving
    ( HasState "wasNewQ" Bool
    , HasSource "wasNewQ" Bool
    , HasSink "wasNewQ" Bool
    ) via
    ReaderRef (Field "wasNewQ" "ctx" (MonadReader (ReaderT (BuilderCtx s p) (ST s))))
  deriving
    ( HasState "qcons" (QCons.ConsState Int Int)
    , HasSource "qcons" (QCons.ConsState Int Int)
    , HasSink "qcons" (QCons.ConsState Int Int)
    ) via
    ReaderRef (Field "qcons" "ctx" (MonadReader (ReaderT (BuilderCtx s p) (ST s))))
  deriving
    ( HasState "tcons" (TConsState s p)
    , HasSource "tcons" (TConsState s p)
    , HasSink "tcons" (TConsState s p)
    ) via
    ReaderRef (Field "tcons" "ctx" (MonadReader (ReaderT (BuilderCtx s p) (ST s))))
  deriving
    ( HasState "inTcons" (InTConsState s p)
    , HasSource "inTcons" (InTConsState s p)
    , HasSink "inTcons" (InTConsState s p)
    ) via
    ReaderRef (Field "inTcons" "ctx" (MonadReader (ReaderT (BuilderCtx s p) (ST s))))
  deriving
    ( HasState "algDomain" (GrowableArray (LSTArray s) (Mix, Int))
    , HasSource "algDomain" (GrowableArray (LSTArray s) (Mix, Int))
    , HasSink "algDomain" (GrowableArray (LSTArray s) (Mix, Int))
    ) via
    ReaderRef (Field "algDomain" "ctx" (MonadReader (ReaderT (BuilderCtx s p) (ST s))))
  deriving
    ( HasIxedSource "algDomainArr" Int (Mix, Int)
    ) via
    IxStateUnsafe (ReaderT (BuilderCtx s p) (ST s))
    ( Rename "arr"
    ( Field "arr" "algDomain"
    ( ReaderRef
    ( Field "algDomain" "ctx"
    ( MonadReader
    ( ReaderT (BuilderCtx s p) (ST s)
    ))))))

newQ :: Int -> Builder s p Int
newQ q = do
  put @"wasNewQ" True
  i <- QCons.cons @"qcons" q
  -- traceShow ("newQ", i, q)$ return ()
  return i
{-# INLINE newQ #-}

newT :: forall s p. (Eq p, Hashable p, Show p) => Term' p -> Builder s p Int
newT t = do
  i <- TCons.consKMod @"tcons" t t id
  -- traceShow ("newT", i, t)$ return ()
  return i
{-# INLINE newT #-}

newInT :: forall s p. (Eq p, Hashable p, Show p) => BackTerm' p -> Builder s p Int
newInT t = do
  i <- InTCons.consKMod @"inTcons" @(ReaderT (BuilderCtx s p) (ST s)) t t id
  -- traceShow ("newInT", i, t)$ return ()
  return i
{-# INLINE newInT #-}

getUnresolvedBack :: Mix -> Bool
getUnresolvedBack (PureA (b, _)) = b
getUnresolvedBack (PureQ (QRef _ _ _ b)) = b
getUnresolvedBack _ = False
{-# INLINE getUnresolvedBack #-}

{-# INLINABLE qacEnv #-}
qacEnv :: forall s p.
  (Eq p, Hashable p, Show p)
  => Array Int Int -> Term p (Bool, Int) (Bool, (Mix, Int)) -> Builder s p (Mix, Int)
qacEnv states = qac
  where 
  qac :: Term p (Bool, Int) (Bool, (Mix, Int)) -> Builder s p (Mix, Int)
  qac LTrue = do
    c <- newT LTrue
    return (PureQ (QRef False c c False), c)
  qac (Predicate p) = do
    c <- newT$ Predicate p
    return (PureA (False, c), c)
  qac (State bq@(back, q)) = do
    c <- newT$ State q
    return (PureQ (QRef back (states!q) c back), c)
  qac (And ts)
    | null qs0 = do
        c <- newT$ And$ fmap (snd . snd) ts
        return (PureA (False, c), c)
    | null as =
        if back
        then do
          c <- newT$ And$ fmap (snd . snd) ts
          q <- newInT$ And$ NE.fromList qs0
          return (PureQ (QRef True q c False), c)
        else do
          q <- newInT$ And$ NE.fromList qs0
          s <- newQ q
          c <- newT$ State s
          return (PureQ (QRef False q c False), c)
    | otherwise = do
        a'@(_, a) <- case as of
          [a] -> return a
          _:_:_ -> fmap (False,)$ newT$ And$ NE.fromList$ map snd as
        case qsBoth of
          [(b, QRef _ q qc b2)] -> do
            c <- newT$ And$ qc :| [a]
            return (AndMix (QRef back q qc (b || b2)) a', c)
          _:_:_
            | back -> do
               q <- newInT$ And$ NE.fromList qs0
               qc <- newT$ And$ NE.fromList$ map snd qcs
               c <- newT$ And$ qc :| [a]
               return (AndMix (QRef True q qc False) a', c)
            | otherwise -> do
               q <- newInT$ And$ NE.fromList qs0
               s <- newQ q
               qc <- newT$ State s
               c <- newT$ And$ qc :| [a]
               return (AndMix (QRef False q qc False) a', c)
    where
    lts = NE.toList ts
    qsBoth = flip mapMaybe lts$ \(b, fst -> mix) -> (b,) <$> case mix of
      PureQ qref -> Just qref
      AndMix qref _ -> Just qref
      _ -> Nothing
    as = flip mapMaybe lts$ \(b, mix) -> case mix of
      (PureA (b2, aref), _) -> Just (b || b2, aref)
      (OrMix _ _, cref) -> Just (b, cref)
      (AndMix _ (b2, aref), _) -> Just (b || b2, aref)
      _ -> Nothing
    qs0 = map (\(b, QRef _ q _ b2) -> (b || b2, q)) qsBoth
    qcs = map (\(b, QRef _ _ qc b2) -> (b || b2, qc)) qsBoth
    back = all (\(b, QRef qb _ _ _) -> b || qb) qsBoth
  qac (Or ts)
    | null qs0 = do
        c <- newT$ Or$ fmap (snd . snd) ts
        return (PureA (False, c), c)
    | null as =
        if back
        then do
          c <- newT$ Or$ fmap (snd . snd) ts
          q <- newInT$ Or$ NE.fromList qs0
          return (PureQ (QRef True q c False), c)
        else do
          q <- newInT$ Or$ NE.fromList qs0
          s <- newQ q
          c <- newT$ State s
          return (PureQ (QRef False q c False), c)
    | otherwise = do
        a'@(_, a) <- case as of
          [a] -> return a
          _:_:_ -> fmap (False,)$ newT$ Or$ NE.fromList$ map snd as
        case qsBoth of
          [(b, QRef _ q qc b2)] -> do
            c <- newT$ Or$ qc :| [a]
            return (OrMix (QRef back q qc (b || b2)) a', c)
          _:_:_
            | back -> do
               q <- newInT$ Or$ NE.fromList qs0
               qc <- newT$ Or$ NE.fromList$ map snd qcs
               c <- newT$ Or$ qc :| [a]
               return (OrMix (QRef True q qc False) a', c)
            | otherwise -> do
               q <- newInT$ Or$ NE.fromList qs0
               s <- newQ q
               qc <- newT$ State s
               c <- newT$ Or$ qc :| [a]
               return (OrMix (QRef False q qc False) a', c)
    where
    lts = NE.toList ts
    qsBoth = flip mapMaybe lts$ \(b, fst -> mix) -> (b,) <$> case mix of
      PureQ qref -> Just qref
      OrMix qref _ -> Just qref
      _ -> Nothing
    as = flip mapMaybe lts$ \(b, mix) -> case mix of
      (PureA (b2, aref), _) -> Just (b || b2, aref)
      (AndMix _ _, cref) -> Just (b, cref)
      (OrMix _ (b2, aref), _) -> Just (b || b2, aref)
      _ -> Nothing
    qs0 = map (\(b, QRef _ q _ b2) -> (b || b2, q)) qsBoth
    qcs = map (\(b, QRef _ _ qc b2) -> (b || b2, qc)) qsBoth
    back = all (\(b, QRef qb _ _ _) -> b || qb) qsBoth


{-# INLINABLE extract #-}
extract
  :: Show p => Term p (Bool, Int) (Bool, (Mix, Int))
  -> Free (Term p (Bool, Int)) (Bool, (Mix, Int))
extract LTrue = Free LTrue
extract (Predicate p) = Free (Predicate p)
extract (State q) = Free (State q)
extract (And ts) = case extracted of
  [x] -> x
  (x:xs) -> Free$ And$ x :| xs
  where
  lts = NE.toList ts
  candidates = flip map lts$ \case
    x@(_, (OrMix _ a, _)) -> (Just a, x)
    x@(_, (PureA a, _)) -> (Just a, x)
    x -> (Nothing, x)
  grouped = groupWith (fmap snd . fst)$ sortWith (fmap snd . fst) candidates
  extracted = flip map grouped$ \case
    [x] -> Pure$ snd x
    ((a, x):axs) -> case a of
      Nothing -> Free$ And$ NE.map Pure$ x:|xs
      Just (ab0, a) -> case xs' of
        Right xs' -> Free$ Or$
          Pure (False, (PureA (ab, a), a)) :| [Free$ And$ NE.map Pure xs']
        Left x -> Pure x
        where
        xs' = for (x:|xs)$ \case
          (b, (OrMix q@(QRef _ _ qc _) _, _)) -> Right (b, (PureQ q, qc))
          x -> Left x
        ab = or$ ab0 : map (fst . fromJust . fst) axs
      where
      xs = map snd axs
extract (Or ts) = case extracted of
  [x] -> x
  (x:xs) -> Free$ Or$ x :| xs
  where
  lts = NE.toList ts
  candidates = flip map lts$ \case
    x@(_, (AndMix _ a, _)) -> (Just a, x)
    x@(_, (PureA a, _)) -> (Just a, x)
    x -> (Nothing, x)
  grouped = groupWith fst$ sortWith fst candidates
  extracted = flip map grouped$ \case
    [x] -> Pure$ snd x
    ((a, x):axs) -> case a of
      Nothing -> Free$ Or$ NE.map Pure$ x:|xs
      Just (ab0, a) -> case xs' of
        Right xs' -> Free$ And$
          Pure (False, (PureA (ab, a), a)) :| [Free$ Or$ NE.map Pure xs']
        Left x -> Pure x
        where
        xs' = for (x:|xs)$ \case
          (b, (AndMix q@(QRef _ _ qc _) _, _)) -> Right (b, (PureQ q, qc))
          x -> Left x
        ab = or$ ab0 : map (fst . fromJust . fst) axs
      where
      xs = map snd axs


{-# INLINABLE extractAndQac #-}
extractAndQac
  :: (Show p, Eq p, Hashable p)
  => Array Int Int -> Term p (Bool, Int) (Bool, (Mix, Int)) -> Builder s p (Mix, Int)
extractAndQac (qacEnv -> qac) = helper where
  helper (extract -> x) = fmap snd$ flip iterM x$
    sequence >=> qac >=> return . (False,)

{-# INLINABLE goblin2 #-}
goblin2 :: forall p. (Show p, Eq p, Hashable p)
  => Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int
  -> Afa (Array Int (Term p Int Int)) (Array Int Int) Int
goblin2 afa@(Afa terms states init) = Afa terms' states' init
  where
  (terms', states') = runST action
  extractAndQac' = extractAndQac states

  action :: forall s. ST s (Array Int (Term p Int Int), Array Int Int)
  action = do
    qconsV <- newSTRef$ QCons.ConsState (numElements states) (HM.fromList$ map swap$ assocs states) (reverse$ elems states)
    tconsV <- newSTRef TCons.consState0
    algDomainV <- runIdentityT (GArray.new (numElements terms * 2)) >>= newSTRef
    wasNewQV <- newSTRef False

    inTarr <- runIdentityT$ GArray.new (numElements terms * 2)
    inTarr <- runIdentityT$ foldM (flip GArray.append) inTarr (elems terms)
    inTconsV <- newSTRef$ InTCons.ConsState (HM.fromList$ map swap$ assocs terms) inTarr

    let ctx = BuilderCtx qconsV inTconsV tconsV algDomainV wasNewQV
    runBuilder (myCata (numElements terms) 0) ctx

    (GrowableArray n ixMapM) <- readSTRef algDomainV
    ixMap :: Array Int (Mix, Int) <- runIdentityT$ unsafeFreeze ixMapM

    qs <- QCons.consResult <$> readSTRef qconsV

    (,)
      <$> (listArrayN . TCons.consResult <$> readSTRef tconsV)
      <*> (fmap (snd . (ixMap!)) . listArrayN . QCons.consResult <$> readSTRef qconsV)

  myCata :: forall s. Int -> Int -> Builder s p ()
  myCata stageEnd stageStart = thisStage stageStart where
    thisStage i = do
      InTCons.ConsState _ (GrowableArray n arr) <- get @"inTcons"
      when (i < n)$ do
        -- when (i `mod` 100 == 0)$ traceShow i$ return ()
        if i == stageEnd
          then do
            wasNewQ <- get @"wasNewQ"
            when wasNewQ$ do
              put @"wasNewQ" False
              cataOne arr i
              myCata n (i + 1)
          else cataOne arr i >> thisStage (i + 1)

    cataOne arr i = do
      ti <- coerce @(ReaderT (BuilderCtx s p) (ST s) _)$ readArray arr i
      a <- cataStep @"algDomainArr" (traversed._2) extractAndQac' ti
      -- traceShow (i, ti, a)$ return ()
      get @"algDomain"
        >>= coerce @(ReaderT (BuilderCtx s p) (ST s) _) . GArray.append a
        >>= put @"algDomain"

toDotGoblin
  :: Show p
  => Bool
  -> Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int
  -> String
toDotGoblin cyclic (Afa mterms states init) = unlines
  [ "digraph afa {"
  , "  graph [nodesep=0.2];"
  , "  node [fontsize=20];"
  , unlines [[i|  m#{j} -> #{c} [penwidth=#{if w then "3.0" else "1.0"}]|] | (j, t) <- assocs mterms, (w, c) <- mchilds t]
  , unlines [[i|  q#{j} -> m#{q}|] | (j, q) <- assocs states]
  , unlines [[i|  q#{j} [style=filled, fillcolor=#{if j == init then "yellow" else "pink"}]|] | (j, _) <- assocs states]
  , unlines [[i|  m#{j} [style=filled, #{mstyle j t}]|] | (j, t) <- assocs mterms]
  , "}"
  ]
  where
  mchilds t = case t of
    State (b, q) -> [(b, if cyclic then [i|q#{q}|] else [i|Q#{q}|])]
    _ -> [(b, [i|m#{c}|]) | (b, c) <- toList t]

  mstyle j (And _) = "shape=rectangle, fillcolor=lightgoldenrod1"
  mstyle j (Or _) = "shape=rectangle, fillcolor=lightblue"
  mstyle j (Predicate p) = [i|shape=rectangle, fillcolor=lightgrey, label=m#{j}p#{p}|]
  mstyle j (State _) = "shape=rectangle, fillcolor=white"
  mstyle j LTrue = "shape=rectangle, fillcolor=green"
