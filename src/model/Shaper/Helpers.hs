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
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Shaper.Helpers where

import Control.Monad ((<=<))
import Control.Monad.Free (Free, iterM)
import Data.Fix (Fix (Fix))
import Shaper (IsTree, MonadFn (..), MonadFn', ask)

import InversionOfControl.TypeDict
import InversionOfControl.Lift

type BuildInheritShareD d x r m =
  Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
    :+: Name "buildTree" (MonadFn' [d|buildTree|] x r m)
    :+: Name "shareTree" (MonadFn' [d|shareTree|] r r m)
    :+: End
buildInheritShare ::
  forall (d :: TypeDict) x r m n rec.
  ( ToConstraint (BuildInheritShareD d x r m)
  , rec ~ Unwrap [d|rec|]
  ) =>
  x ->
  m r
buildInheritShare x =
  monadfn @(Mk IsTree [d|rec|]) () >>= \case
    True -> [d|monadfn|buildTree|] x
    False -> [d|monadfn|buildTree|] x >>= [d|monadfn|shareTree|]

type BuildD d f r m = Name "build" (MonadFn' [d|build|] (f r) r m) :+: End
buildFix ::
  forall d f r m.
  (ToConstraint (BuildD d f r m), Traversable f) =>
  Fix f ->
  m r
buildFix (Fix fa) = traverse (buildFix @d) fa >>= [d|monadfn|build|]

buildFree ::
  forall d f r m.
  (ToConstraint (BuildD d f r m), Traversable f) =>
  Free f r ->
  m r
buildFree = iterM ([d|monadfn|build|] <=< sequence)
