{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Delit where

import Afa.Term as Term
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict

data Delit (xBuild :: *) (xDeref :: *)
type DelitKBuild q v r x = Explicit (Term q v r) r x
type DelitKDeref q v r x = Explicit r (Term q v r) x

instance
  ( MonadFn0 (DelitKBuild q v r xBuild) m
  , MonadFn0 (DelitKDeref q v r xDeref) m
  ) =>
  MonadFn0 (Explicit (Term q v r) r (Delit xBuild xDeref)) m
  where
  monadfn0 = \case
    fr@(Not r) ->
      deref r >>= \case
        LTrue -> build LFalse
        LFalse -> build LTrue
        Not r' -> return r'
        _ -> build fr
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
      deref = monadfn0 @(DelitKDeref q v r xDeref)
      build = monadfn0 @(DelitKBuild q v r xBuild)

data IORefDelitO (d :: * -> Pean -> *) (cont :: *) (n :: Pean)
type instance
  Definition (IORefDelitO d cont n) =
    Name "build" ('K n (Delit (Unwrap [gcn|build|]) (Unwrap [gcn|deref|])))
      :+: Follow (d cont n)
