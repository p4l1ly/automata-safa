{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Separated where

import Afa.Finalful.STerm (Term(..))
import Shaper
import Data.Kind (Constraint)
import Shaper.Helpers
import Data.Functor ((<&>))
import Data.Traversable (for)

import InversionOfControl.TypeDict
import InversionOfControl.Lift

data AQ1 r = A1 r | Q1 r | AQAnd1 r r deriving (Show, Functor, Foldable, Traversable)
data AQ r = A r | Q r | AQAnd r r | AQOr [AQ1 r] deriving (Show, Functor, Foldable, Traversable)

type TrySeparateAlgD d m = TrySeparateAlgD_ d m (TrySeparateAlgA d [g|q|] [g|v|] [g|r|]) [g|q|] [g|v|] [g|r|]
type TrySeparateAlgA :: TypeDict -> * -> * -> * -> TypeDict
type TrySeparateAlgA d q v r =  -- keyword aliases
  Name "rec" (Mk (MfnK r (AQ r)) [d|rec|])
    :+: Name "self" (Mk (MfnK () r) [d|rec|])
    :+: Name "fail" (Mk (MfnK (Term q v (AQ r)) (AQ r)) [d|fail|])
    :+: Name "buildD"
          ( Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
              :+: Name "buildTree" (Mk (MfnK (Term q v r) r) [d|buildTree|])
              :+: d
          )
    :+: End
type TrySeparateAlgD_ :: TypeDict -> (* -> *) -> TypeDict -> * -> * -> * -> TypeDict
type TrySeparateAlgD_ d m d' q v r =
  Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d' ~ TrySeparateAlgA d q v r)
  :+: Name "rec"
        ( Name "self" (MonadFn [d'|self|] m)
            :+: Name "rec" (MonadFn [d'|rec|] m)
            :+: Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
            :+: End
        )
  :+: Name "fail" (MonadFn [d'|fail|] m)
  :+: Name "build" (Remove "isTree" (BuildInheritShareD [g'|buildD|] (Term q v r) r m))
  :+: End
trySeparateAlg ::
  forall d q v r m d'.
  ToConstraint (TrySeparateAlgD_ d m d' q v r) =>
  Term q v r -> m (AQ r)
trySeparateAlg LTrue = [d'|ask|self|] <&> A
trySeparateAlg LFalse = [d'|ask|self|] <&> A
trySeparateAlg (State _) = [d'|ask|self|] <&> Q
trySeparateAlg (Var _) = [d'|ask|self|] <&> A
trySeparateAlg fr = traverse [d'|monadfn|rec|] fr >>= \case
  (Not (A _)) -> [d'|ask|self|] <&> A
  (Or (A _) (A _)) -> [d'|ask|self|] <&> A
  (Or (Q _) (Q _)) -> [d'|ask|self|] <&> Q
  (Or r1 r2) -> return $ AQOr $ disjunct r1 ++ disjunct r2
  (And (A _) (A _)) -> [d'|ask|self|] <&> A
  (And (Q _) (Q _)) -> [d'|ask|self|] <&> Q
  (And (A a) (Q q)) -> return $ AQAnd a q
  (And (Q q) (A a)) -> return $ AQAnd a q
  (And (A a1) (AQAnd a2 q)) -> buildInheritShare @[g'|buildD|] (And a1 a2) <&> (`AQAnd` q)
  (And (AQAnd a1 q) (A a2)) -> buildInheritShare @[g'|buildD|] (And a1 a2) <&> (`AQAnd` q)
  (And (Q q1) (AQAnd a q2)) -> buildInheritShare @[g'|buildD|] (And q1 q2) <&> AQAnd a
  (And (AQAnd a q1) (Q q2)) -> buildInheritShare @[g'|buildD|] (And q1 q2) <&> AQAnd a
  (And (AQAnd a1 q1) (AQAnd a2 q2)) -> AQAnd
    <$> buildInheritShare @[g'|buildD|] (And q1 q2)
    <*> buildInheritShare @[g'|buildD|] (And a1 a2)
  x -> [d'|monadfn|fail|] x

disjunct :: AQ r -> [AQ1 r]
disjunct (AQOr xs) = xs
disjunct (AQAnd a q) = [AQAnd1 a q]
disjunct (A a) = [A1 a]
disjunct (Q q) = [Q1 q]

type BoomSeparateAlgD d m = BoomSeparateAlgD_ d m (BoomSeparateAlgA d [g|q|] [g|v|] [g|r|]) [g|q|] [g|v|] [g|r|]
type BoomSeparateAlgA d q v r =  -- keyword aliases
  Name "rec" (Mk (MfnK r (AQ r)) [d|rec|])
    :+: Name "self" (Mk (MfnK () r) [d|rec|])
    :+: Name "buildD"
          ( Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
              :+: Name "buildTree" (Mk (MfnK (Term q v r) r) [d|buildTree|])
              :+: d
          )
    :+: End
type BoomSeparateAlgD_ :: TypeDict -> (* -> *) -> TypeDict -> * -> * -> * -> TypeDict
type BoomSeparateAlgD_ d m d' q v r =
  Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d' ~ BoomSeparateAlgA d q v r)
  :+: Name "rec"
        ( Name "self" (MonadFn [d'|self|] m)
            :+: Name "rec" (MonadFn [d'|rec|] m)
            :+: Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
            :+: End
        )
  :+: Name "build" (Remove "isTree" (BuildInheritShareD [g'|buildD|] (Term q v r) r m))
  :+: End
boomSeparateAlg ::
  forall d q v r m d'.
  ToConstraint (BoomSeparateAlgD_ d m d' q v r) =>
  Term q v r -> m (AQ r)
boomSeparateAlg LTrue = [d'|ask|self|] <&> A
boomSeparateAlg LFalse = [d'|ask|self|] <&> A
boomSeparateAlg (State _) = [d'|ask|self|] <&> Q
boomSeparateAlg (Var _) = [d'|ask|self|] <&> A
boomSeparateAlg fr = traverse [d'|monadfn|rec|] fr >>= \case
  Not (A _) -> [d'|ask|self|] <&> A
  Or (A _) (A _) -> [d'|ask|self|] <&> A
  Or (Q _) (Q _) -> [d'|ask|self|] <&> Q
  Or r1 r2 -> return $ AQOr $ disjunct r1 ++ disjunct r2
  And (A _) (A _) -> [d'|ask|self|] <&> A
  And (Q _) (Q _) -> [d'|ask|self|] <&> Q
  And (A a) (Q q) -> return $ AQAnd a q
  And (Q q) (A a) -> return $ AQAnd a q
  And (A a1) (AQAnd a2 q) -> buildInheritShare @[g'|buildD|] (And a1 a2) <&> (`AQAnd` q)
  And (AQAnd a1 q) (A a2) -> buildInheritShare @[g'|buildD|] (And a1 a2) <&> (`AQAnd` q)
  And (Q q1) (AQAnd a q2) -> buildInheritShare @[g'|buildD|] (And q1 q2) <&> AQAnd a
  And (AQAnd a q1) (Q q2) -> buildInheritShare @[g'|buildD|] (And q1 q2) <&> AQAnd a
  And (AQAnd a1 q1) (AQAnd a2 q2) -> AQAnd
   <$> buildInheritShare @[g'|buildD|] (And q1 q2)
   <*> buildInheritShare @[g'|buildD|] (And a1 a2)
  Not (Q _) -> error "unsupported: negation above states"
  Not (AQAnd _ _) -> error "unsupported: negation above states"
  Not (AQOr _) -> error "unsupported: negation above states"
  And (A a) (AQOr conjuncts) -> AQOr <$> (`traverse` conjuncts) \case
    A1 a2 -> A1 <$> buildInheritShare @[g'|buildD|] (And a a2)
    Q1 q -> return $ AQAnd1 a q
    AQAnd1 a2 q -> (`AQAnd1` q) <$> buildInheritShare @[g'|buildD|] (And a a2)
  And (Q q) (AQOr conjuncts) -> AQOr <$> (`traverse` conjuncts) \case
    A1 a -> return $ AQAnd1 a q
    Q1 q2 -> Q1 <$> buildInheritShare @[g'|buildD|] (And q q2)
    AQAnd1 a q2 -> AQAnd1 a <$> buildInheritShare @[g'|buildD|] (And q q2)
  And (AQAnd a q) (AQOr conjuncts) -> AQOr <$> (`traverse` conjuncts) \case
    A1 a2 -> (`AQAnd1` q) <$> buildInheritShare @[g'|buildD|] (And a a2)
    Q1 q2 -> AQAnd1 a <$> buildInheritShare @[g'|buildD|] (And q q2)
    AQAnd1 a2 q2 ->
      AQAnd1
        <$> buildInheritShare @[g'|buildD|] (And a a2)
        <*> buildInheritShare @[g'|buildD|] (And q q2)
  And (AQOr conjuncts) (A a) -> AQOr <$> (`traverse` conjuncts) \case
    A1 a2 -> A1 <$> buildInheritShare @[g'|buildD|] (And a a2)
    Q1 q -> return $ AQAnd1 a q
    AQAnd1 a2 q -> (`AQAnd1` q) <$> buildInheritShare @[g'|buildD|] (And a a2)
  And (AQOr conjuncts) (Q q) -> AQOr <$> (`traverse` conjuncts) \case
    A1 a -> return $ AQAnd1 a q
    Q1 q2 -> Q1 <$> buildInheritShare @[g'|buildD|] (And q q2)
    AQAnd1 a q2 -> AQAnd1 a <$> buildInheritShare @[g'|buildD|] (And q q2)
  And (AQOr conjuncts) (AQAnd a q) -> AQOr <$> (`traverse` conjuncts) \case
    A1 a2 -> (`AQAnd1` q) <$> buildInheritShare @[g'|buildD|] (And a a2)
    Q1 q2 -> AQAnd1 a <$> buildInheritShare @[g'|buildD|] (And q q2)
    AQAnd1 a2 q2 ->
      AQAnd1
        <$> buildInheritShare @[g'|buildD|] (And a a2)
        <*> buildInheritShare @[g'|buildD|] (And q q2)
  And (AQOr conjuncts1) (AQOr conjuncts2) -> AQOr <$>
    sequence
      [ case aq1 of
          A1 a -> case aq2 of
            A1 a2 -> A1 <$> buildInheritShare @[g'|buildD|] (And a a2)
            Q1 q -> return $ AQAnd1 a q
            AQAnd1 a2 q -> (`AQAnd1` q) <$> buildInheritShare @[g'|buildD|] (And a a2)
          Q1 q -> case aq2 of
            A1 a -> return $ AQAnd1 a q
            Q1 q2 -> Q1 <$> buildInheritShare @[g'|buildD|] (And q q2)
            AQAnd1 a q2 -> AQAnd1 a <$> buildInheritShare @[g'|buildD|] (And q q2)
          AQAnd1 a q -> case aq2 of
            A1 a2 -> (`AQAnd1` q) <$> buildInheritShare @[g'|buildD|] (And a a2)
            Q1 q2 -> AQAnd1 a <$> buildInheritShare @[g'|buildD|] (And q q2)
            AQAnd1 a2 q2 ->
              AQAnd1
                <$> buildInheritShare @[g'|buildD|] (And a a2)
                <*> buildInheritShare @[g'|buildD|] (And q q2)
      | aq1 <- conjuncts1
      , aq2 <- conjuncts2
      ]
  _ -> error "should've been matched without traverse"
