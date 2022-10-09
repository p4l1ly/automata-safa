{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.Ltle2 where

import Afa.Finalful.STerm
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Composition
import Data.IORef
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import qualified Ltl
import Shaper hiding (ask)
import Shaper.Helpers
import TypeDict

pattern LTrueF = Free LTrue

pattern LFalseF = Free LFalse

pattern StateF q = Free (State q)

pattern VarF i = Free (Var i)

pattern NotF t = Free (Not t)

pattern AndF t1 t2 = Free (And t1 t2)

pattern OrF t1 t2 = Free (Or t1 t2)

type Build r m = ReaderT (IORef Int, IORef [r]) m
data SyncedV v = SyncV | OtherV v deriving (Show, Eq)

newState :: forall n r m. (Monad m, MLift n m IO) => Build r m Int
newState = do
  stateCountV <- asks fst
  lift do
    q <- mlift @n $ readIORef stateCountV
    mlift @n $ writeIORef stateCountV (q + 1)
    return q

setTransition :: forall n r m. (Monad m, MLift n m IO) => r -> Build r m ()
setTransition transition = do
  transitionsV <- asks snd
  lift $ mlift @n $ modifyIORef transitionsV (transition :)

newAcyclicState :: forall n r m. (Monad m, MLift n m IO) => r -> Build r m Int
newAcyclicState transition = do
  (stateCountV, transitionsV) <- ask
  lift do
    q <- mlift @n $ readIORef stateCountV
    mlift @n $ writeIORef stateCountV (q + 1)
    mlift @n $ modifyIORef transitionsV (transition :)
    return q

type ParseD d m = ParseD_ d m (ParseA d [g|r|]) [g|r|] [g|n|]
type ParseA d r =
  Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
    :+: Name "buildShared" (Mk (MfnK (Term Int (SyncedV Int) r) r) [d|buildShared|])
    :+: Name "buildTree" (Mk (MfnK (Term Int (SyncedV Int) r) r) [d|buildTree|])
    :+: Name
          "buildTreeD"
          (Name "build" (Mk (MfnK (Term Int (SyncedV Int) r) r) [d|buildTree|]) :+: d)
    :+: End
type ParseD_ (d :: TypeDict) (m :: * -> *) (d' :: TypeDict) (r :: *) n =
  D.Name "aliases" (r ~ [g|r|], n ~ [g|n|], d' ~ ParseA d r)
    :|: D.Name "" (MonadFn [d'|shareTree|] m)
    :|: D.Name "" (MonadFn [d'|buildShared|] m)
    :|: D.Name "" (MonadFn [d'|buildTree|] m)
    :|: D.Name "" (BuildD [g'|buildTreeD|] (Term Int (SyncedV Int)) r m)
    :|: D.Name "" (MLift n m IO)
    :|: D.End

algebra ::
  forall d m r d' n. (D.ToConstraint (ParseD_ d m d' r n)) => Ltl.Ltl r -> Build r m r
algebra Ltl.LTrue = lift do [d'|monadfn|buildShared|] LTrue
algebra Ltl.LFalse = lift do [d'|monadfn|buildShared|] LFalse
algebra (Ltl.Var i) = lift do [d'|monadfn|buildShared|] $ Var $ OtherV i
algebra (Ltl.Not afa) = lift do [d'|monadfn|buildShared|] $ Not afa
algebra (Ltl.And afas) = lift do
  true <- [d'|monadfn|buildTree|] LTrue
  buildFree @[g'|buildTreeD|] $ foldr (AndF . Pure) (Pure true) afas
algebra (Ltl.Or afas) = lift do
  false <- [d'|monadfn|buildTree|] LFalse
  buildFree @[g'|buildTreeD|] $ foldr (OrF . Pure) (Pure false) afas
algebra (Ltl.Next afa) = do
  q <- newAcyclicState @n afa
  lift $ buildFree @[g'|buildTreeD|] $ AndF (StateF q) (NotF $ VarF SyncV)
algebra (Ltl.Until predicate end) = do
  q <- newState @n
  qr <- lift do [d'|monadfn|buildShared|] (State q)
  let f = OrF (Pure end) (AndF (Pure predicate) (AndF (NotF $ VarF SyncV) (Pure qr)))
  t <- lift $ buildFree @[g'|buildTreeD|] f
  setTransition @n t
  return qr
algebra (Ltl.WeakUntil predicate end) = do
  q1 <- newState @n
  q2 <- newState @n
  predicate' <- lift do
    buildFree @[g'|buildTreeD|] (AndF (Pure predicate) (NotF $ VarF SyncV))
      >>= [d'|monadfn|shareTree|]
  globx <- lift do
    buildFree @[g'|buildTreeD|] (AndF (Pure predicate') (StateF q2))
      >>= [d'|monadfn|shareTree|]
  result <- lift do
    buildFree @[g'|buildTreeD|]
      (OrF (Pure globx) (OrF (Pure end) (AndF (Pure predicate') (StateF q1))))
      >>= [d'|monadfn|shareTree|]
  setTransition @n result
  setTransition @n
    =<< lift do buildFree @[g'|buildTreeD|] (OrF (VarF SyncV) (Pure globx))
  return result
algebra (Ltl.Globally afa) = do
  q <- newState @n
  result <- lift do
    buildFree @[g'|buildTreeD|]
      (AndF (Pure afa) (OrF (VarF SyncV) (StateF q)))
      >>= [d'|monadfn|shareTree|]
  setTransition @n result
  return result
algebra (Ltl.Finally afa) = do
  q <- newState @n
  result <- lift do
    buildFree @[g'|buildTreeD|]
      (OrF (Pure afa) (AndF (NotF $ VarF SyncV) (StateF q)))
      >>= [d'|monadfn|shareTree|]
  setTransition @n result
  return result
algebra (Ltl.Release _ _) = error "Release not supported here! Use deRelease before."
