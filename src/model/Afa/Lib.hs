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

module Afa.Lib where

import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import Afa.Term
import Data.Fix
import Control.Monad.Free
import Control.Monad

type BuildI k f r m =
  ( MonadFn k m
  , f r ~ Param (Unwrap k)
  , r ~ Result (Unwrap k)
  , Traversable f
  )

buildFix :: forall k f r m. BuildI k f r m => Fix f -> m r
buildFix (Fix fa) = traverse (buildFix @k) fa >>= monadfn @k

buildFree :: forall k f r m.
  ( MonadFn k m
  , f r ~ Param (Unwrap k)
  , r ~ Result (Unwrap k)
  , Traversable f
  ) =>
  Free f r -> m r
buildFree = iterM (monadfn @k <=< sequence)

data UnInitStateA d
type instance Definition (UnInitStateA d) =
  Name "deref" (Inherit (Explicit $r [g|term|]) [g|deref|])
    :+: End

data UnInitStateI d d1 (m :: * -> *)
type instance Definition (UnInitStateI d d1 m) =
  Name "all" (d1 ~ UnInitStateA d, MonadFn [g1|deref|] m)
    :+: End

unInitState ::
  forall d m d1 q v r.
  ( ToConstraint (Follow (UnInitStateI d d1 m))
  , Term q v r ~ [g|term|]
  ) =>
  (r, r, (Int, Int -> q, Int -> r, q -> Int)) ->
  m (r, r, (Int, Int -> q, Int -> r, q -> Int))
unInitState afa@(init, final, states@(_, _, i2r, q2i)) = do
  monadfn @[g1|deref|] init >>= \case
    (State q :: Term q v r) -> return (i2r $ q2i q, final, states)
    _ -> return afa
