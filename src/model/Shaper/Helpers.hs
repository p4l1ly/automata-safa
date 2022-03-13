{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Shaper.Helpers where

import Control.Monad ((<=<))
import Control.Monad.Free (Free, iterM)
import Data.Fix (Fix (Fix))
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Shaper (IsTree, Mk, MonadFn (..), MonadFn', ask)
import TypeDict (Tag, TypeDict, d)

import Lift (K (K), LiftCount, Pean (Zero), Unwrap)

type BuildInheritShareD d x r m =
  D.Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
    :|: D.Name "buildTree" (MonadFn' [d|buildTree|] x r m)
    :|: D.Name "shareTree" (MonadFn' [d|shareTree|] r r m)
    :|: D.End
buildInheritShare ::
  forall (d :: TypeDict) x r m n rec.
  ( D.ToConstraint (BuildInheritShareD d x r m)
  , rec ~ Unwrap (Tag "rec" d)
  ) =>
  x ->
  m r
buildInheritShare x =
  monadfn @(Mk IsTree [d|rec|]) () >>= \case
    True -> [d|monadfn|buildTree|] x
    False -> [d|monadfn|buildTree|] x >>= [d|monadfn|shareTree|]

type BuildD d f r m = D.Name "build" (MonadFn' [d|build|] (f r) r m) :|: D.End
buildFix ::
  forall d f r m.
  (D.ToConstraint (BuildD d f r m), Traversable f) =>
  Fix f ->
  m r
buildFix (Fix fa) = traverse (buildFix @d) fa >>= [d|monadfn|build|]

buildFree ::
  forall d f r m.
  (D.ToConstraint (BuildD d f r m), Traversable f) =>
  Free f r ->
  m r
buildFree = iterM ([d|monadfn|build|] <=< sequence)
