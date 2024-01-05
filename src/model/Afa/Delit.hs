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

data Delit (xBuild :: *) (xDeref :: *) (xIsTree :: *) (xShare :: *) (xReplace :: *)
type DelitKBuild q v r x = Explicit (Term q v r) r x
type DelitKDeref q v r x = Explicit r (Term q v r) x
type DelitKIsTree r x = Explicit r Bool x
type DelitKShare r x = Explicit r r x
type DelitKReplace q v r x = Explicit (r, Term q v r) r x

instance
  ( MonadFn0 (DelitKBuild q v r xBuild) m
  , MonadFn0 (DelitKDeref q v r xDeref) m
  , MonadFn0 (DelitKIsTree r xIsTree) m
  , MonadFn0 (DelitKShare r xShare) m
  , MonadFn0 (DelitKReplace q v r xReplace) m
  ) =>
  MonadFn0 (Explicit (Term q v r) r (Delit xBuild xDeref xIsTree xShare xReplace)) m
  where
  monadfn0 = \case
    fr@(Not r) ->
      deref r >>= \case
        LTrue -> build LFalse
        LFalse -> build LTrue
        Not r' -> do
          isTree r >>= \case
            True -> return r'
            False -> do
              r'' <- share r'
              replace (r, Not r'')
              return r''
        _unmodifiedTerm -> build fr
    fr@(And a b) ->
      deref a >>= \case
        LTrue -> return b
        LFalse -> build LFalse
        _unmodifiedTerm ->
          deref b >>= \case
            LTrue -> return a
            LFalse -> build LFalse
            _unmodifiedTerm -> build fr
    fr@(Or a b) ->
      deref a >>= \case
        LFalse -> return b
        LTrue -> build LTrue
        _unmodifiedTerm ->
          deref b >>= \case
            LFalse -> return a
            LTrue -> build LTrue
            _unmodifiedTerm -> build fr
    fr -> build fr
    where
      deref = monadfn0 @(DelitKDeref q v r xDeref)
      build = monadfn0 @(DelitKBuild q v r xBuild)
      isTree = monadfn0 @(DelitKIsTree r xIsTree)
      share = monadfn0 @(DelitKShare r xShare)
      replace = monadfn0 @(DelitKReplace q v r xReplace)

data IORefDelitO (d :: * -> *) (cont :: *)
type instance
  Definition (IORefDelitO d cont) =
    Name "build" (Delit [gc|build|] [gc|deref|] [gc|isTree|] [gc|share|] [gc|replace|])
      :+: Follow (d cont)
