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

module Afa.Build where

import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import Afa.Term
import Data.Fix
import Control.Monad.Free
import Control.Monad

-- Build -------------------------------------------------------------------------------

type BuildD k f r m =
  ( MonadFn k m
  , f r ~ Param (Unwrap k)
  , r ~ Result (Unwrap k)
  , Traversable f
  )

buildFix :: forall k f r m. BuildD k f r m => Fix f -> m r
buildFix (Fix fa) = traverse (buildFix @k) fa >>= monadfn @k

buildFree :: forall k f r m. BuildD k f r m => Free f r -> m r
buildFree = iterM (monadfn @k <=< sequence)

---- BuildShareShared ------------------------------------------------------------------

data BuildShareSharedTermO d
type instance Definition (BuildShareSharedTermO d) =
  Name "fr'" [g|term|]
    :+: Name "r'" $r
    :+: Name "r" $r
    :+: Follow d

data BuildShareSharedA d
type instance Definition (BuildShareSharedA d) =
  Name "build" (Inherit (Explicit [g|fr'|] [g|r'|]) [k|build|])
    :+: Name "share" (Inherit (Explicit [g|r'|] [g|r'|]) [k|share|])
    :+: Name "isTree" (Inherit (Explicit [g|r|] Bool) [k|isTree|])
    :+: End

data BuildShareSharedI d d1 (m :: * -> *)
type instance Definition (BuildShareSharedI d d1 m) =
  Name "all"
    ( d1 ~ BuildShareSharedA d
    , MonadFn [g1|build|] m
    , MonadFn [g1|share|] m
    , MonadFn [g1|isTree|] m
    )
    :+: End

type BuildShareSharedD d m =
  ToConstraint (Follow (BuildShareSharedI d (BuildShareSharedA d) m))

buildShareShared :: forall d d1 m.
  ToConstraint (Follow (BuildShareSharedI d d1 m)) =>
  [g|r|] -> [g|fr'|] -> m [g|r'|]
buildShareShared r fr' = do
  r' <- monadfn @[g1|build|] fr'
  monadfn @[g1|isTree|] r >>= \case
    True -> return r'
    False -> monadfn @[g1|share|] r'

