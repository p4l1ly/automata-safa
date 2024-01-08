{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Separate where

import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import qualified InversionOfControl.Recur as R
import qualified InversionOfControl.MapRecur as MR
import Afa.Term hiding (Q)
import Afa.Build
import Data.Functor
import Afa.States
import Control.Monad.Except
import Control.Monad.Free

data AQ1 r = A1 r | Q1 r | AQAnd1 r r
data AQ r = A r | Q r | AQAnd r r | AQOr [AQ1 r]

aqToTuples :: r -> AQ r -> [(r, r)]
aqToTuples ltrue = \case
  A ar -> [(ar, ltrue)]
  Q qr -> [(ltrue, qr)]
  AQAnd ar qr -> [(ar, qr)]
  AQOr conjs -> conjs <&> \case
    A1 ar -> (ar, ltrue)
    Q1 qr -> (ltrue, qr)
    AQAnd1 ar qr -> (ar, qr)

disjunct :: AQ r -> [AQ1 r]
disjunct (AQOr xs) = xs
disjunct (AQAnd a q) = [AQAnd1 a q]
disjunct (A a) = [A1 a]
disjunct (Q q) = [Q1 q]

data TrySeparateAlgA d
type instance Definition (TrySeparateAlgA d) =
  Name "fail" (Inherit (Explicit () (AQ $r)) [k|fail|])
    :+: Name "dBuild" (BuildShareSharedTermO d :: *)
    :+: End

type TrySeparateAlgI d d1 (m :: * -> *) =
  ( d1 ~ TrySeparateAlgA d
  , BuildShareSharedD ([g1|dBuild|] :: *) m
  , Term $q $v $r ~ [g|term|]
  , MonadFn [g1|fail|] m
  )

type TrySeparateAlgD d (m :: * -> *) = TrySeparateAlgI d (TrySeparateAlgA d) m

trySeparateAlg ::
  forall d m d1.
  TrySeparateAlgI d d1 m =>
  ($r -> m (AQ $r)) ->
  ($r, [g|term|]) ->
  m (AQ $r)
trySeparateAlg rec (r0, term) = case term of
  LTrue -> return $ A r0
  LFalse -> return $ A r0
  (State _) -> return $ Q r0
  (Var _) -> return $ A r0
  fr -> traverse rec fr >>= \case
    (Not (A _)) -> return $ A r0
    (Or (A _) (A _)) -> return $ A r0
    (Or (Q _) (Q _)) -> return $ Q r0
    (Or r1 r2) -> return $ AQOr $ disjunct r1 ++ disjunct r2
    (And (A _) (A _)) -> return $ A r0
    (And (Q _) (Q _)) -> return $ Q r0
    (And (A a) (Q q)) -> return $ AQAnd a q
    (And (Q q) (A a)) -> return $ AQAnd a q
    (And (A a1) (AQAnd a2 q)) -> buildShareShared @[g1|dBuild|] r0 (And a1 a2) <&> (`AQAnd` q)
    (And (AQAnd a1 q) (A a2)) -> buildShareShared @[g1|dBuild|] r0 (And a1 a2) <&> (`AQAnd` q)
    (And (Q q1) (AQAnd a q2)) -> buildShareShared @[g1|dBuild|] r0 (And q1 q2) <&> AQAnd a
    (And (AQAnd a q1) (Q q2)) -> buildShareShared @[g1|dBuild|] r0 (And q1 q2) <&> AQAnd a
    (And (AQAnd a1 q1) (AQAnd a2 q2)) -> AQAnd
      <$> buildShareShared @[g1|dBuild|] r0 (And q1 q2)
      <*> buildShareShared @[g1|dBuild|] r0 (And a1 a2)
    x -> monadfn @[g1|fail|] ()

data Fail
instance Monad m => MonadFn0 (Explicit e a Fail) (ExceptT e m) where
  monadfn0 = throwError

data SeparateO d
type instance Definition (SeparateO d) =
  Name "qs" (RTraversed $qs [($r, $r)])
    :+: Follow d

data TrySeparateA d
type instance Definition (TrySeparateA d) =
  Name "rec" (R.Explicit (Inc [k|rcata|]) Zero $r ($r, [g|term|]))
    :+: Name "build" (Inherit (Explicit [g|term|] $r) [k|build|])
    :+: End

data TrySeparateA' d
type instance Definition (TrySeparateA' d) =
  Name "fail" Fail :+: Follow (LiftUp d)

type TrySeparateI d d1 m =
  ( d1 ~ TrySeparateA d
  , TrySeparateAlgD (TrySeparateA' d) (ExceptT () m)
  , R.Recur [g1|rec|] (AQ $r) (ExceptT () m)
  , MonadFn [g1|build|] m
  )

type TrySeparateD d m = TrySeparateI d (TrySeparateA d) m

trySeparate ::
  forall d d1 m qs qs'.
  ( TrySeparateI d d1 m
  , RTraversable qs $q $r [($r, $r)] qs'
  ) =>
  qs -> m (Maybe qs')
trySeparate qs = do
  ltrue <- monadfn @[g1|build|] LTrue
  result <- runExceptT @() $
    R.runRecur @[g1|rec|] (trySeparateAlg @(LiftUp (TrySeparateA' d))) \sep -> do
      traverseR (fmap (aqToTuples ltrue) . sep) qs
  case result of
    Left _ -> return Nothing
    Right qs' -> return $ Just qs'

data BoomSeparateAlgA d
type instance Definition (BoomSeparateAlgA d) =
  Name "dBuild" (BuildShareSharedTermO d :: *)
    :+: Name "share" (Inherit (Explicit $r $r) [k|share|])
    :+: End

type BoomSeparateAlgI d d1 (m :: * -> *) =
  ( d1 ~ BoomSeparateAlgA d
  , BuildShareSharedD ([g1|dBuild|] :: *) m
  , MonadFn [g1|share|] m
  , Term $q $v $r ~ [g|term|]
  )

type BoomSeparateAlgD d m = BoomSeparateAlgI d (BoomSeparateAlgA d) m

boomSeparateAlg ::
  forall d d1 m.
  BoomSeparateAlgI d d1 m =>
  ($r -> m (AQ $r)) ->
  ($r, [g|term|]) ->
  m (AQ $r)
boomSeparateAlg rec (r0, term) = case term of
  LTrue -> return $ A r0
  LFalse -> return $ A r0
  (State _) -> return $ Q r0
  (Var _) -> return $ A r0
  fr -> traverse rec fr >>= \case
    Not (A _) -> return $ A r0
    Or (A _) (A _) -> return $ A r0
    Or (Q _) (Q _) -> return $ Q r0
    Or r1 r2 -> return $ AQOr $ disjunct r1 ++ disjunct r2
    And (A _) (A _) -> return $ A r0
    And (Q _) (Q _) -> return $ Q r0
    And (A a) (Q q) -> return $ AQAnd a q
    And (Q q) (A a) -> return $ AQAnd a q
    And (A a1) (AQAnd a2 q) -> buildShareShared @[g1|dBuild|] r0 (And a1 a2) <&> (`AQAnd` q)
    And (AQAnd a1 q) (A a2) -> buildShareShared @[g1|dBuild|] r0 (And a1 a2) <&> (`AQAnd` q)
    And (Q q1) (AQAnd a q2) -> buildShareShared @[g1|dBuild|] r0 (And q1 q2) <&> AQAnd a
    And (AQAnd a q1) (Q q2) -> buildShareShared @[g1|dBuild|] r0 (And q1 q2) <&> AQAnd a
    And (AQAnd a1 q1) (AQAnd a2 q2) -> AQAnd
      <$> buildShareShared @[g1|dBuild|] r0 (And q1 q2)
      <*> buildShareShared @[g1|dBuild|] r0 (And a1 a2)
    Not (Q _) -> error "unsupported: negation above states"
    Not (AQAnd _ _) -> error "unsupported: negation above states"
    Not (AQOr _) -> error "unsupported: negation above states"
    And (A a) (AQOr conjuncts) -> do
      a <- monadfn @[g1|share|] a
      AQOr <$> (`traverse` conjuncts) \case
        A1 a2 -> A1 <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
        Q1 q -> return $ AQAnd1 a q
        AQAnd1 a2 q -> (`AQAnd1` q) <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
    And (Q q) (AQOr conjuncts) -> do
      q <- monadfn @[g1|share|] q
      AQOr <$> (`traverse` conjuncts) \case
        A1 a -> return $ AQAnd1 a q
        Q1 q2 -> Q1 <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
        AQAnd1 a q2 -> AQAnd1 a <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
    And (AQAnd a q) (AQOr conjuncts) -> do
      a <- monadfn @[g1|share|] a
      q <- monadfn @[g1|share|] q
      AQOr <$> (`traverse` conjuncts) \case
        A1 a2 -> (`AQAnd1` q) <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
        Q1 q2 -> AQAnd1 a <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
        AQAnd1 a2 q2 ->
          AQAnd1
            <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
            <*> buildShareShared @[g1|dBuild|] r0 (And q q2)
    And (AQOr conjuncts) (A a) -> do
      a <- monadfn @[g1|share|] a
      AQOr <$> (`traverse` conjuncts) \case
        A1 a2 -> A1 <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
        Q1 q -> return $ AQAnd1 a q
        AQAnd1 a2 q -> (`AQAnd1` q) <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
    And (AQOr conjuncts) (Q q) -> do
      q <- monadfn @[g1|share|] q
      AQOr <$> (`traverse` conjuncts) \case
        A1 a -> return $ AQAnd1 a q
        Q1 q2 -> Q1 <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
        AQAnd1 a q2 -> AQAnd1 a <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
    And (AQOr conjuncts) (AQAnd a q) -> do
      a <- monadfn @[g1|share|] a
      q <- monadfn @[g1|share|] q
      AQOr <$> (`traverse` conjuncts) \case
        A1 a2 -> (`AQAnd1` q) <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
        Q1 q2 -> AQAnd1 a <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
        AQAnd1 a2 q2 ->
          AQAnd1
            <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
            <*> buildShareShared @[g1|dBuild|] r0 (And q q2)
    And (AQOr conjuncts1) (AQOr conjuncts2) -> do
      let shareConjunct (A1 a) = A1 <$> monadfn @[g1|share|] a
          shareConjunct (Q1 q) = Q1 <$> monadfn @[g1|share|] q
          shareConjunct (AQAnd1 a q) = AQAnd1 <$> monadfn @[g1|share|] a <*> monadfn @[g1|share|] q
      conjuncts1 <- traverse shareConjunct conjuncts1
      conjuncts2 <- traverse shareConjunct conjuncts2
      AQOr <$>
        sequence
          [ case aq1 of
              A1 a -> case aq2 of
                A1 a2 -> A1 <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
                Q1 q -> return $ AQAnd1 a q
                AQAnd1 a2 q -> (`AQAnd1` q) <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
              Q1 q -> case aq2 of
                A1 a -> return $ AQAnd1 a q
                Q1 q2 -> Q1 <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
                AQAnd1 a q2 -> AQAnd1 a <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
              AQAnd1 a q -> case aq2 of
                A1 a2 -> (`AQAnd1` q) <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
                Q1 q2 -> AQAnd1 a <$> buildShareShared @[g1|dBuild|] r0 (And q q2)
                AQAnd1 a2 q2 ->
                  AQAnd1
                    <$> buildShareShared @[g1|dBuild|] r0 (And a a2)
                    <*> buildShareShared @[g1|dBuild|] r0 (And q q2)
          | aq1 <- conjuncts1
          , aq2 <- conjuncts2
          ]
    _ -> error "should've been matched without traverse"

data BoomSeparateA d
type instance Definition (BoomSeparateA d) =
  Name "rec" (R.Explicit [k|rcata|] Zero $r ($r, [g|term|]))
    :+: Name "build" (Inherit (Explicit [g|term|] $r) [k|build|])
    :+: End

type BoomSeparateI d d1 m =
  ( d1 ~ BoomSeparateA d
  , BoomSeparateAlgD d m
  , R.Recur [g1|rec|] (AQ $r) m
  , MonadFn [g1|build|] m
  )

type BoomSeparateD d m = BoomSeparateI d (BoomSeparateA d) m

boomSeparate ::
  forall d d1 m qs qs'.
  ( BoomSeparateI d d1 m
  , RTraversable qs $q $r [($r, $r)] qs'
  ) =>
  qs -> m qs'
boomSeparate qs = do
  ltrue <- monadfn @[g1|build|] LTrue
  R.runRecur @[g1|rec|] (boomSeparateAlg @(LiftUp d)) \sep -> do
    traverseR (fmap (aqToTuples ltrue) . sep) qs

data UnseparateO d
type instance Definition (UnseparateO d) =
  Name "qs" (RTraversed $qs $r)
    :+: Follow d

data UnseparateA d
type instance Definition (UnseparateA d) =
  Name "build" (Inherit (Explicit [g|term|] $r) [k|build|])
    :+: End

type UnseparateI d d1 m =
  ( d1 ~ UnseparateA d
  , MonadFn [g1|build|] m
  )

unseparate ::
  forall d d1 m qs qs'.
  ( UnseparateI d d1 m
  , RTraversable $qs $q [($r, $r)] $r (RTraversed $qs $r)
  , Term $q $v $r ~ [g|term|]
  ) =>
  $qs -> m (RTraversed $qs $r)
unseparate qs = do
  let step (ar, qr) = Free . Or (Free (And (Pure ar) (Pure qr)))
  flip traverseR qs $ buildFree @[g1|build|] . foldr step (Free LFalse)
