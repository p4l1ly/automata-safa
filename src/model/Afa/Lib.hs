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

module Afa.Lib where

import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import qualified InversionOfControl.Recur as R
import qualified InversionOfControl.MapRecur as MR
import Afa.Term
import Data.Fix
import Control.Monad.Free
import Control.Monad
import Afa.States
import Data.Bifunctor
import Control.Monad.Trans
import Data.Hashable
import Data.Monoid
import qualified Data.HashSet as HS
import Data.Function.Syntax ((.:))
import Data.Kind
import Data.List
import Data.Functor
import qualified Data.HashMap.Strict as HM
import Data.Function.Apply
import Data.Maybe

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

-- RemoveSingleInit --------------------------------------------------------------------

data RemoveSingleInitA d
type instance Definition (RemoveSingleInitA d) =
  Name "deref" (Inherit (Explicit $r [g|term|]) [k|deref|])
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
    :+: Name "build" (Inherit (Explicit [gs|term'|] [gs|r'|]) [k|build|])
    :+: Name "deref" (Inherit (Explicit [gs|r'|] [gs|term'|]) [k|deref|])
    :+: Name "mapK" ([g|mapRecFun|] '[Q] :: *)
    :+: Name "mapF" ($q -> AddInitQ $q)
    :+: Name "map" (MR.Explicit [k|mapRec|] $r [gs|r'|] (Creation [gs|mapK|] [gs|mapF|]))
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


-- DeMorganAlg -------------------------------------------------------------------------

data DeMorganAlgI d d1 (m :: * -> *)
type instance Definition (DeMorganAlgI d d1 m) =
  Name "all"
    ( d1 ~ BuildShareSharedTermO d
    , BuildShareSharedD d1 m
    , Term $q $v $r ~ [g|term|]
    )
    :+: End

type DeMorganAlgD d (m :: * -> *) =
  ToConstraint (Follow (DeMorganAlgI d (BuildShareSharedTermO d) m))

deMorganAlg ::
  forall d m d1.
  (ToConstraint (Follow (DeMorganAlgI d d1 m))) =>
  ($r -> m $r) -> ($r, Term $q $v $r) -> m $r
deMorganAlg rec (r0, term) = case term of
  LTrue -> buildShareShared @d1 r0 LFalse
  LFalse -> buildShareShared @d1 r0 LTrue
  State q -> return r0
  Var v -> buildShareShared @d1 r0 (Not r0)
  Not r -> return r
  And a b -> Or <$> rec a <*> rec b >>= buildShareShared @d1 r0
  Or a b ->
    And <$> rec a <*> rec b >>= buildShareShared @d1 r0

-- complement --------------------------------------------------------------------------

data ComplementA d
type instance Definition (ComplementA d) =
  Name "rec" (R.Explicit [k|rcata|] Zero $r ($r, [g|term|]))
    :+: Name "build" (Inherit (Explicit [g|term|] $r) [k|build|])
    :+: End

complement ::
  forall d d1 qs m.
  ( d1 ~ ComplementA d
  , DeMorganAlgD d m
  , R.Recur [g1|rec|] $r m
  , States qs $q $r
  , RTraversable qs $r $r qs
  , SplitFinalsD d m
  , Hashable $q
  , MonadFn [g1|build|] m
  , Show $q
  ) =>
  ($r, $r, qs) ->
  m (Maybe ($r, $r, qs))
complement (init, final, qs) = do
  (init', qs') <- R.runRecur @[g1|rec|] (deMorganAlg @(LiftUp d)) \deMorgan -> do
      (,) <$> deMorgan init <*> traverseR deMorgan qs
  (nonfinals, complex) <- splitFinals @d final
  case complex of
    Nothing -> do
      let nonfinalsHS = HS.fromList nonfinals
      let nonfinals' = [q | (q, _) <- stateList qs', not (q `HS.member` nonfinalsHS)]
      let nonfinal' = foldr (Fix .: And . Fix . Not . Fix . State) (Fix LTrue) nonfinals'
      nonfinalR' <- buildFix @[g1|build|] nonfinal'
      return $ Just (init', nonfinalR', qs')
    _ -> return Nothing

-- splitFinals -------------------------------------------------------------------------

data SplitFinalsA d
type instance Definition (SplitFinalsA d) =
  Name "deref" (Inherit (Explicit $r [g|term|]) [k|deref|])
    :+: Name "rec" (R.Explicit [k|rcata|] Zero $r ($r, [g|term|]))
    :+: End

data SplitFinalsI d d1 d2 (m :: * -> *)
type instance Definition (SplitFinalsI d d1 d2 m) =
  Name "all"
    ( d2 ~ BuildShareSharedTermO d
    , BuildShareSharedD d2 m
    , d1 ~ SplitFinalsA d
    , Term $q $v $r ~ [g|term|]
    , MonadFn [g1|deref|] m
    , R.Recur [g1|rec|] ((Any, Endo [$q]), Maybe $r) m
    )
    :+: End

type SplitFinalsD d m =
  ToConstraint (Follow (SplitFinalsI d (SplitFinalsA d) (BuildShareSharedTermO d) m))

splitFinals ::
  forall d m d1 d2.
  ToConstraint (Follow (SplitFinalsI d d1 d2 m)) =>
  $r -> m ([$q], Maybe $r)
splitFinals final =
  R.runRecur @[g1|rec|] alg \rec -> do
    ((_, nonfinals), complex) <- rec final
    return (appEndo nonfinals [], complex)
  where
    alg rec (r0, term) = case term of
      Not r -> do
        lift (monadfn @[g1|deref|] r) >>= \case
          State q -> return ((Any True, Endo (q :)), Nothing)
          _ -> return self'
      And r1 r2 -> do
        (qs1, mcomplex1) <- rec r1
        (qs2, mcomplex2) <- rec r2
        (qs1 <> qs2,) <$> case (mcomplex1, mcomplex2) of
          (Nothing, Nothing) -> return Nothing
          (Nothing, Just complex2) -> return $ Just complex2
          (Just complex1, Nothing) -> return $ Just complex1
          (Just complex1, Just complex2)
            | getAny (fst qs1) && getAny (fst qs2) ->
                Just <$> lift (buildShareShared @d2 r0 $ And complex1 complex2)
            | otherwise -> return $ Just r0
      LTrue -> return ((Any True, Endo id), Nothing)
      _ -> return self'
      where
        self' = ((Any False, Endo id), Just r0)

-- unshare -----------------------------------------------------------------------------

data UnshareA d
type instance Definition (UnshareA d) =
  Name "build" (Inherit (Explicit [g|term|] $r) [k|build|])
    :+: Name "rec" (R.Explicit [k|cata|] Zero $r [g|term|])
    :+: End

unshare :: forall d d1 m qs.
  ( d1 ~ UnshareA d
  , Term $q $v $r ~ [g|term|]
  , MonadFn [g1|build|] m
  , R.Recur [g1|rec|] $r m
  , RTraversable qs $r $r qs
  ) =>
  ($r, $r, qs) -> m ($r, $r, qs)
unshare (init, final, qs) = do
  R.runRecur @[g1|rec|]
    (\rec t -> lift . monadfn @[g1|build|] =<< traverse rec t)
    (\rec -> (,,) <$> rec init <*> rec final <*> traverseR rec qs)


-- toDnf -------------------------------------------------------------------------------

type ToDnfAlgD d (m :: * -> *) = () :: Constraint

toDnfAlg :: forall d q v r m.
  Applicative m =>
  ((Bool, r) -> m [[(Either q v, Bool)]]) ->
  (Bool, Term q v r) ->
  m [[(Either q v, Bool)]]
toDnfAlg rec = \case
  (False, LTrue) -> pure []
  (True, LTrue) -> pure [[]]
  (False, LFalse) -> pure [[]]
  (True, LFalse) -> pure []
  (b, State q) -> pure [[(Left q, b)]]
  (b, Var v) -> pure [[(Right v, b)]]
  (False, Not a) -> rec (True, a)
  (True, Not a) -> rec (False, a)
  (False, And a b) ->
    (++) <$> rec (False, a) <*> rec (False, b)
  (True, And a b) ->
    productConcat <$> rec (True, a) <*> rec (True, b)
  (False, Or a b) -> do
    productConcat <$> rec (False, a) <*> rec (False, b)
  (True, Or a b) ->
    (++) <$> rec (True, a) <*> rec (True, b)

productConcat :: [[a]] -> [[a]] -> [[a]]
productConcat xs ys = [x ++ y | x <- xs, y <- ys]

singleToDnf :: forall d m rec build qs.
  ( rec ~ R.Explicit [k|pcata|] Zero (Bool, $r) (Bool, [g|term|])
  , build ~ Inherit (Explicit [g|term|] $r) [k|build|]
  , Term $q $v $r ~ [g|term|]
  , R.Recur rec [[(Either $q $v, Bool)]] m
  , MonadFn build m
  , ToDnfAlgD d m
  , Ord $q
  , Ord $v
  ) =>
  $r -> m $r
singleToDnf x = do
  R.runRecur @rec (toDnfAlg @(LiftUp d)) \rec -> do
    cubes <- rec (True, x)
    let cubes' = buildDisj $ map buildCube $ mapMaybe sortCube cubes
    lift $ buildFix @build cubes'

sortCube ::
  (Ord q, Ord v) =>
  [(Either q v, Bool)] -> Maybe [(Either q v, Bool)]
sortCube = removeDuplicates . sort
  where
    removeDuplicates [] = Just []
    removeDuplicates [x] = Just [x]
    removeDuplicates ((x1, b1) : rest@((x2, b2) : _))
      | x1 /= x2 = ((x1, b1) :) <$> removeDuplicates rest
      | b1 == b2 = removeDuplicates rest
      | otherwise = Nothing

buildCube :: [(Either q v, Bool)] -> Fix (Term q v)
buildCube cube =
  foldr (Fix .: And) (Fix LTrue) $
    cube <&> \(qv, sgn) ->
      (if sgn then id else Fix . Not)
        case qv of
          Left q -> Fix (State q)
          Right v -> Fix (Var v)

buildDisj :: [Fix (Term q v)] -> Fix (Term q v)
buildDisj = foldr (Fix .: Or) (Fix LFalse)
