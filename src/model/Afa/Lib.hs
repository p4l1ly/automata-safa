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

module Afa.Lib where

import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import qualified InversionOfControl.MapRecur as MR
import Afa.Term
import Data.Fix
import Control.Monad.Free
import Control.Monad
import Afa.States
import Data.Bifunctor
import Control.Monad.Trans

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

-- RemoveSingleInit -------------------------------------------------------------------------

data RemoveSingleInitA d
type instance Definition (RemoveSingleInitA d) =
  Name "deref" (Inherit (Explicit $r [g|term|]) [g|deref|])
    :+: End

data RemoveSingleInitI d d1 (m :: * -> *) q v r
type instance Definition (RemoveSingleInitI d d1 m q v r) =
  Name "all" (d1 ~ RemoveSingleInitA d, MonadFn [g1|deref|] m, Term q v r ~ [g|term|])
    :+: End

removeSingleInit ::
  forall d m d1 q v r qs.
  ( ToConstraint (Follow (RemoveSingleInitI d d1 m q v r))
  , States qs q r
  ) =>
  (r, r, qs) ->
  m (r, r, qs)
removeSingleInit afa@(init, final, qs) = do
  monadfn @[g1|deref|] init >>= \case
    (State q :: Term q v r) -> return (transition qs q, final, qs)
    _ -> return afa

-- AddInitState ------------------------------------------------------------------------

data AddInitQ q = AddInitInit | AddInitOther !q deriving (Eq, Show)
data AddInitQs qs r = AddInitQs qs r deriving (Eq, Show)

instance States qs q r => States (AddInitQs qs r) (AddInitQ q) r where
  stateList (AddInitQs qs r) =
    (AddInitInit, r) : map (first AddInitOther) (stateList qs)
  transition (AddInitQs qs r) AddInitInit = r
  transition (AddInitQs qs r) (AddInitOther q) = transition qs q

instance RTraversable qs r r' qs' =>
  RTraversable (AddInitQs qs r) r r' (AddInitQs qs' r') where
  traverseR f (AddInitQs qs r) = AddInitQs <$> traverseR f qs <*> f r

data AddInitO d
type instance Definition (AddInitO d) =
  Name "term" (Term (AddInitQ $q) $v (Get "r'" (Follow (AddInitA d)))) :+: Follow d

data AddInitA d
type instance Definition (AddInitA d) =
  Name "r'" (Creation ([g|mapRecFunR'|] $r '[Q]) ($q -> AddInitQ $q))
    :+: Name "term'" (Term (AddInitQ $q) $v [gs|r'|])
    :+: Name "build" (Inherit (Explicit [gs|term'|] [gs|r'|]) [g|build|])
    :+: Name "deref" (Inherit (Explicit [gs|r'|] [gs|term'|]) [g|deref|])
    :+: Name "mapK" ([g|mapRecFun|] '[Q] :: *)
    :+: Name "mapF" ($q -> AddInitQ $q)
    :+: Name "map" (MR.Explicit [g|mapRec|] $r [gs|r'|] (Creation [gs|mapK|] [gs|mapF|]))
    :+: End

data AddInitI d d1 (m :: * -> *)
type instance Definition (AddInitI d d1 m) =
  Name "all"
    ( d1 ~ AddInitA d
    , MonadFn [g1|build|] m
    , MonadFn [g1|deref|] m
    , Create [g1|mapK|] [g1|mapF|]
    , MR.Recur [g1|map|] m
    , Term $q $v $r ~ [g|term|]
    )
    :+: End
addInit ::
  forall d m d1 qs qs'.
  ( ToConstraint (Follow (AddInitI d d1 m))
  , RTraversable qs $r [g1|r'|] qs'
  ) =>
  ($r, $r, qs) ->
  m ([g1|r'|], [g1|r'|], AddInitQs qs' [g1|r'|])
addInit afa@(init, final, qs) = do
  let mfun = create @[g1|mapK|] (AddInitOther @($q))
  MR.runRecur @[g1|map|] mfun \mapAddInit -> do
    init' <- mapAddInit init
    final' <- mapAddInit final
    qs' <- traverseR mapAddInit qs
    lift (monadfn @[g1|deref|] init') >>= \case
      State q -> do
        lfalse <- lift $ monadfn @[g1|build|] LFalse
        return (init', final', AddInitQs qs' lfalse)
      _ -> do
        init'' <- lift $ monadfn @[g1|build|] (State AddInitInit)
        final'' <- lift $ buildFree @[g1|build|] $
          Free $ And (Free $ Not (Pure init'')) (Pure final')
        return (init'', final'', AddInitQs qs' init')
