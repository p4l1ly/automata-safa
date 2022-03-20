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

module Afa.Separated where

import Afa.Finalful.STerm (Term(..))
import TypeDict
import Shaper
import Data.Kind (Constraint)
import Shaper.Helpers
import DepDict ( ToConstraint, DepDict((:|:)) )
import qualified DepDict as D
import Data.Functor ((<&>))

data AQ1 r = A1 r | Q1 r | AQAnd1 r r deriving (Show, Functor, Foldable, Traversable)
data AQ r = A r | Q r | AQAnd r r | AQOr [AQ1 r] deriving (Show, Functor, Foldable, Traversable)

type TrySeparateAlgD d m = TrySeparateAlgD_ d m (TrySeparateAlgA d [g|q|] [g|v|] [g|r|]) [g|q|] [g|v|] [g|r|]
type TrySeparateAlgA d q v r =  -- keyword aliases
  Name "rec" (Mk (MfnK r (AQ r)) [d|rec|])
    :+: Name "self" (Mk (MfnK () r) [d|rec|])
    :+: Name "deref" (Mk (MfnK r (Term q v r)) [d|deref|])
    :+: Name "fail" (Mk (MfnK (Term q v (AQ r)) (AQ r)) [d|fail|])
    :+: Name "buildD"
          ( Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
              :+: Name "buildTree" (Mk (MfnK (Term q v r) r) [d|buildTree|])
              :+: d
          )
    :+: End
type TrySeparateAlgD_ :: TypeDict -> (* -> *) -> TypeDict -> * -> * -> * -> DepDict
type TrySeparateAlgD_ d m d' q v r =
  D.Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d' ~ TrySeparateAlgA d q v r)
  :|: D.Name "rec"
        ( D.Name "self" (MonadFn [d'|self|] m)
            :|: D.Name "rec" (MonadFn [d'|rec|] m)
            :|: D.Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
            :|: D.End
        )
  :|: D.Name "deref" (MonadFn [d'|deref|] m)
  :|: D.Name "fail" (MonadFn [d'|fail|] m)
  :|: D.Name "build" (D.Remove "isTree" (BuildInheritShareD [g'|buildD|] (Term q v r) r m))
  :|: D.End
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
