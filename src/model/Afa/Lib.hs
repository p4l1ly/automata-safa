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
import Afa.States hiding (Q)
import qualified Afa.States as Qs
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
import Afa.Build
import Data.Traversable
import Data.Array
import Control.Lens (itraverse)
import Data.Either
import Control.Monad.Identity
import InversionOfControl.LiftN
import Data.IORef

-- RemoveSingleInit --------------------------------------------------------------------

data RemoveSingleInitA d
type instance Definition (RemoveSingleInitA d) =
  Name "deref" (Inherit (Explicit $r [g|term|]) [k|deref|])
    :+: End

type RemoveSingleInitI d d1 m =
  ( d1 ~ RemoveSingleInitA d
  , MonadFn [g1|deref|] m
  , Term $q $v $r ~ [g|term|]
  , States $qs $q $r
  )

removeSingleInit ::
  forall d m d1.
  RemoveSingleInitI d d1 m =>
  ($r, $r, $qs) ->
  m ($r, $r, $qs)
removeSingleInit afa@(init, final, qs) = do
  monadfn @[g1|deref|] init >>= \case
    (State q :: Term q v r) -> return (transition qs q, final, qs)
    _ -> return afa

-- AddInitState ------------------------------------------------------------------------

data AddOneQ q = AddedQ | OriginalQ !q deriving (Eq, Show)
data AddOneQs qs = AddOneQs qs (R qs)

instance States qs q r => States (AddOneQs qs) (AddOneQ q) r where
  stateList (AddOneQs qs r) =
    (AddedQ, r) : map (first OriginalQ) (stateList qs)
  transition (AddOneQs qs r) AddedQ = r
  transition (AddOneQs qs r) (OriginalQ q) = transition qs q
  redirect (AddOneQs qs r) redirs =
    AddOneQs
      (redirect qs $ map (\(OriginalQ q, r) -> (q, r)) otherRedirs)
      (case initRedirs of [] -> r; _ -> snd $ last initRedirs)
    where
      (initRedirs, otherRedirs) =
        partition (\case (AddedQ, _) -> True; _ -> False) redirs

type instance RTraversed (AddOneQs qs) r' = AddOneQs (RTraversed qs r')
type instance R (AddOneQs qs) = R qs
type instance Qs.Q (AddOneQs qs) = AddOneQ (Qs.Q qs)
instance RTraversable qs q r r' qs' =>
  RTraversable (AddOneQs qs) (AddOneQ q) r r' (AddOneQs qs') where
  traverseQR f (AddOneQs qs r) =
    AddOneQs <$> traverseQR (f . OriginalQ) qs <*> f AddedQ r

data AddInitO d
type instance Definition (AddInitO d) =
  Name "term" (Term (AddOneQ $q) $v (GetF "r'" (AddInitA d)))
    :+: Name "qs" (AddOneQs (RTraversed $qs $rSelf))
    :+: Follow d

data AddInitA d
type instance Definition (AddInitA d) =
  Name "mapF" ($q -> AddOneQ $q)
    :+: Name "r'" (Creation ([g|mapRecFunR'|] $r '[Q]) [gs|mapF|])
    :+: Name "term'" (Term (AddOneQ $q) $v [gs|r'|])
    :+: Name "build" (Inherit (Explicit [gs|term'|] [gs|r'|]) [k|build|])
    :+: Name "deref" (Inherit (Explicit [gs|r'|] [gs|term'|]) [k|deref|])
    :+: Name "mapK" ([g|mapRecFun|] '[Q] :: *)
    :+: Name "map" (MR.Explicit [k|mapRec|] $r [gs|r'|] (Creation [gs|mapK|] [gs|mapF|]))
    :+: Name "qs'" (RTraversed $qs [gs|r'|])
    :+: End

type AddInitI d d1 m =
  ( d1 ~ AddInitA d
  , MonadFn [g1|build|] m
  , MonadFn [g1|deref|] m
  , Create [g1|mapK|] [g1|mapF|]
  , MR.Recur [g1|map|] m
  , Term $q $v $r ~ [g|term|]
  , RTraversable $qs $q $r [g1|r'|] [g1|qs'|]
  )
addInit ::
  forall d m d1 qs'.
  AddInitI d d1 m =>
  ($r, $r, $qs) ->
  m ([g1|r'|], [g1|r'|], AddOneQs [g1|qs'|])
addInit afa@(init, final, qs) = do
  let mfun = create @[g1|mapK|] (OriginalQ @($q))
  MR.runRecur @[g1|map|] mfun \mapAddInit -> do
    init' <- mapAddInit init
    final' <- mapAddInit final
    qs' <- traverseR mapAddInit qs
    lift (monadfn @[g1|deref|] init') >>= \case
      State q -> do
        lfalse <- lift $ monadfn @[g1|build|] LFalse
        return (init', final', AddOneQs qs' lfalse)
      _ -> do
        init'' <- lift $ monadfn @[g1|build|] (State AddedQ)
        final'' <- lift $ buildFree @[g1|build|] $
          Free $ And (Free $ Not (Pure init'')) (Pure final')
        return (init'', final'', AddOneQs qs' init')


-- DeMorganAlg -------------------------------------------------------------------------

type DeMorganAlgI d d1 m =
  ( d1 ~ BuildShareSharedTermO d
  , BuildShareSharedD d1 m
  , Term $q $v $r ~ [g|term|]
  )

type DeMorganAlgD d (m :: * -> *) = DeMorganAlgI d (BuildShareSharedTermO d) m

deMorganAlg ::
  forall d m d1.
  DeMorganAlgI d d1 m =>
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

type ComplementI d d1 m =
  ( d1 ~ ComplementA d
  , DeMorganAlgD d m
  , R.Recur [g1|rec|] $r m
  , States $qs $q $r
  , RTraversable $qs $q $r $r $qs
  , SplitFinalsD d m
  , Hashable $q
  , MonadFn [g1|build|] m
  , Show $q
  )

complement ::
  forall d d1 m.
  ComplementI d d1 m =>
  ($r, $r, $qs) ->
  m (Maybe ($r, $r, $qs))
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

type SplitFinalsI d d1 d2 m =
  ( d2 ~ BuildShareSharedTermO d
  , BuildShareSharedD d2 m
  , d1 ~ SplitFinalsA d
  , Term $q $v $r ~ [g|term|]
  , MonadFn [g1|deref|] m
  , R.Recur [g1|rec|] ((Any, Endo [$q]), Maybe $r) m
  )

type SplitFinalsD d m =
  SplitFinalsI d (SplitFinalsA d) (BuildShareSharedTermO d) m

splitFinals ::
  forall d m d1 d2.
  SplitFinalsI d d1 d2 m =>
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
            | getAny (fst qs1) || getAny (fst qs2) ->
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

type UnshareI d d1 m =
  ( d1 ~ UnshareA d
  , Term $q $v $r ~ [g|term|]
  , MonadFn [g1|build|] m
  , R.Recur [g1|rec|] $r m
  , RTraversable $qs $q $r $r $qs
  )

unshare :: forall d d1 m.
  UnshareI d d1 m => ($r, $r, $qs) -> m ($r, $r, $qs)
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

-- qdnf --------------------------------------------------------------------------------

type QDnfAlgI d d1 m =
  ( d1 ~ BuildShareSharedTermO d
  , BuildShareSharedD d1 m
  , Term $q $v $r ~ [g|term|]
  )

type QDnfAlgD d m = QDnfAlgI d (BuildShareSharedTermO d) m

qdnfAlg ::
  forall d d1 m.
  QDnfAlgI d d1 m =>
  ($r -> m [$r]) -> ($r, [g|term|]) -> m [$r]
qdnfAlg rec (r0, term) = case term of
  LTrue -> return [r0]
  LFalse -> return [r0]
  State _ -> return [r0]
  Var _ -> return [r0]
  fr -> traverse rec fr >>= \case
    (Or disj1 disj2) -> return $ disj1 ++ disj2
    (And [x1] [x2]) -> return [r0]
    (And disj1 disj2) -> sequence [buildShareShared @d1 r0 (And x1 x2) | x1 <- disj1, x2 <- disj2]
    (Not x1) -> error "qdnfAlg: Not unsupported"

data QDnfA d
type instance Definition (QDnfA d) =
  Name "rec" (R.Explicit [k|rcata|] Zero $r ($r, [g|term|]))
    :+: Name "share" (Inherit (Explicit $r $r) [k|share|])
    :+: End
type QDnfI d d1 m =
  ( d1 ~ QDnfA d
  , R.Recur [g1|rec|] [$r] m
  , MonadFn [g1|share|] m
  , QDnfAlgD d m
  )

qdnf ::
  forall d m d1.
  (QDnfI d d1 m, RTraversable $qs $q [($r, $r)] [($r, $r)] $qs) =>
  $qs -> m $qs
qdnf qs = do
  R.runRecur @[g1|rec|] (qdnfAlg @(LiftUp d)) \rec ->
    flip traverseR qs \aqs ->
      concat <$> for aqs \(a, q) ->
        rec q >>= \case
          [q] -> return [(a, q)]
          qs -> do
            a' <- lift $ monadfn @[g1|share|] a
            return $ map (a',) qs

-- qombo -------------------------------------------------------------------------------

data QomboQ q = QomboQ !Int !q deriving (Eq, Show)
newtype QomboQs qs = QomboQs (Array Int qs)
type instance RTraversed (QomboQs qs) r' = QomboQs (RTraversed qs r')
type instance R (QomboQs qs) = R qs
type instance Qs.Q (QomboQs qs) = QomboQ (Qs.Q qs)

instance States qs q r => States (QomboQs qs) (QomboQ q) r where
  stateList (QomboQs qss) = concat $ assocs qss <&> \(i, qs :: qs) ->
    stateList qs <&> first (QomboQ i)
  transition (QomboQs qss) (QomboQ i q) = transition (qss ! i) q
  stateCount (QomboQs qss) = sum $ stateCount <$> qss
  redirect (QomboQs qss) redirs = QomboQs $
    listArray (bounds qss) $
      zipWith
        (\qs redir -> redirect qs (redir []))
        (elems qss)
        (elems partitionedRedirs)
    where
      partitionedRedirs = accumArray (.) id (bounds qss) $
        redirs <&> \(QomboQ i q, r) -> (i, ((q, r) :))

instance RTraversable qs q r r' qs' =>
  RTraversable (QomboQs qs) (QomboQ q) r r' (QomboQs qs') where
  traverseQR fn (QomboQs qss) =
    QomboQs <$> itraverse (\i -> traverseQR (fn . QomboQ i)) qss

data QomboO d
type instance Definition (QomboO d) =
  Name "term" (GetF "term'" (QomboA d))
    :+: Name "qs" (QomboQs (RTraversed $qs $rSelf))
    :+: Follow d

data QomboA d
type instance Definition (QomboA d) =  -- keyword aliases
  Name "r'" (Creation ([g|mapRecFunR'|] $r '[Q]) ($q -> QomboQ $q))
    :+: Name "term'" (Term (QomboQ $q) $v [gs|r'|])
    :+: Name "build" (Inherit (Explicit [gs|term'|] [gs|r'|]) [k|build|])
    :+: Name "mapK" ([g|mapRecFun|] '[Q] :: *)
    :+: Name "mapF" ($q -> QomboQ $q)
    :+: Name "map" (MR.Explicit [k|mapRec|] $r [gs|r'|] (Creation [gs|mapK|] [gs|mapF|]))
    :+: End

type QomboI d d1 m =
  ( d1 ~ QomboA d
  , MonadFn [g1|build|] m
  , Create [g1|mapK|] [g1|mapF|]
  , MR.Recur [g1|map|] m
  , Term $q $v $r ~ [g|term|]
  )
qombo ::
  forall d d1 m qs' freeTerm'.
  ( QomboI d d1 m
  , States $qs $q $r
  , RTraversable $qs $q $r [g1|r'|] qs'
  , freeTerm' ~ Free (Term (QomboQ $q) $v) [g1|r'|]
  ) =>
  ([freeTerm'] -> freeTerm') ->
  [($r, $r, $qs)] ->
  m ([g1|r'|], [g1|r'|], QomboQs qs')
qombo fn afas = do
  let afaCount = length afas
  afas' <- for (zip [0 ..] afas) \(afai, (init, final, qs)) -> do
    let mfun = create @[g1|mapK|] (QomboQ @($q) afai)
    MR.runRecur @[g1|map|] mfun \mapQombo -> do
      init' <- mapQombo init
      final' <- mapQombo final
      qs' <- traverseR mapQombo qs
      return (init', final', qs')
  let (inits', finals', qss') = unzip3 afas'
  let qs' = QomboQs $ listArray (0, afaCount - 1) qss'
  init' <- buildFree @[g1|build|] (fn $ map Pure inits')
  final' <- buildFree @[g1|build|] (foldr (Free .: And . Pure) (Free LTrue) finals')
  return (init', final', qs')


-- delay -------------------------------------------------------------------------------

data UnionQs qs1 qs2 = UnionQs qs1 qs2
type instance RTraversed (UnionQs qs1 qs2) r' = UnionQs (RTraversed qs1 r') (RTraversed qs2 r')
type instance R (UnionQs qs1 qs2) = R qs1
type instance Qs.Q (UnionQs qs1 qs2) = Either (Qs.Q qs1) (Qs.Q qs2)

instance (States qs1 q1 r, States qs2 q2 r) => States (UnionQs qs1 qs2) (Either q1 q2) r where
  stateList (UnionQs qs1 qs2) = map (first Left) (stateList qs1) ++ map (first Right) (stateList qs2)
  transition (UnionQs qs1 qs2) (Left q) = transition qs1 q
  transition (UnionQs qs1 qs2) (Right q) = transition qs2 q
  stateCount (UnionQs qs1 qs2) = stateCount qs1 + stateCount qs2
  redirect (UnionQs qs1 qs2) redirs = UnionQs (redirect qs1 redirs1) (redirect qs2 redirs2)
    where
      (redirs1, redirs2) = partitionEithers (map (\(eq, r) -> bimap (,r) (,r) eq) redirs)

instance (RTraversable qs1 q1 r r' qs1', RTraversable qs2 q2 r r' qs2') =>
  RTraversable (UnionQs qs1 qs2) (Either q1 q2) r r' (UnionQs qs1' qs2') where
  traverseQR fn (UnionQs qs1 qs2) =
    UnionQs
      <$> traverseQR (fn . Left) qs1
      <*> traverseQR (fn . Right) qs2

data DelayO d
type instance Definition (DelayO d) =
  Name "term" (GetF "term'" (DelayA d))
    :+: Name "qs" (GetF "qs'" (DelayA d))
    :+: Follow d

data DelayA d
type instance Definition (DelayA d) =  -- keyword aliases
  Name "r'" (Creation ([g|mapRecFunR'|] $r '[Q]) ($q -> Either Int $q))
    :+: Name "term'" (Term (Either Int $q) $v [gs|r'|])
    :+: Name "qs'" (UnionQs (StateArray [gs|r'|]) (RTraversed $qs [gs|r'|]))
    :+: Name "mapK" ([g|mapRecFunCopy|] '[Q] :: *)
    :+: Name "mapF" ($q -> Either Int $q)
    :+: Name "map" (MR.Explicit [k|mapRecCopy|] $r [gs|r'|] (Creation [gs|mapK|] [gs|mapF|]))
    :+: Name "rec" (R.Explicit (Inc [k|rcata|]) Zero $r ($r, [g|term|]))
    :+: Name "build" (Inherit (Explicit [gs|term'|] [gs|r'|]) [k|build|])
    :+: End

type DelayI d nIO d1 m =
  ( d1 ~ DelayA d
  , Create [g1|mapK|] [g1|mapF|]
  , MR.Recur [g1|map|] m
  , RTraversable $qs $q $r [g1|r'|] (RTraversed $qs [g1|r'|])
  , R.Recur [g1|rec|] [g1|r'|] (MR.Et [g1|map|] m)
  , MonadFn [g1|build|] m
  , LiftN nIO IO m
  , Term $q $v $r ~ [g|term|]
  )
delay ::
  forall d nIO d1 m.
  DelayI d nIO d1 m =>
  ($r, $r, $qs) ->
  ($r -> m Bool) ->
  m ([g1|r'|], [g1|r'|], [g1|qs'|])
delay (init, final, qs) isDelayed = do
  state <- liftn @nIO $ newIORef ([], 1)
  let mfun = create @[g1|mapK|] (Right :: [g1|mapF|])
  (init1, final1, qs1) <- MR.runRecur @[g1|map|] mfun \passR ->
    R.runRecur @[g1|rec|]
      ( \delayR (r0, fr) -> do
          lift (lift $ isDelayed r0) >>= \case
            True -> do
              r0' <- lift $ passR r0
              lift $ lift do
                monadfn @[g1|build|] =<< liftn @nIO do
                  (qrs2, q2Next) <- readIORef state
                  writeIORef state (r0' : qrs2, q2Next + 1)
                  return $ State (Left q2Next)
            False ->
              -- QR Functor
              lift . lift . monadfn @[g1|build|] =<< case fr of
                LTrue -> return LTrue
                LFalse -> return LFalse
                Var v -> return (Var v)
                State q -> return (State (Right q))
                Not x -> Not <$> delayR x
                And x y -> And <$> delayR x <*> delayR y
                Or x y -> Or <$> delayR x <*> delayR y
      )
      (\delayR -> (,,) <$> delayR init <*> lift (passR final) <*> traverseR delayR qs)
  (qrs2, q2Next) <- liftn @nIO $ readIORef state
  let qs2 = StateArray $ listArray (1, q2Next - 1) (reverse qrs2)
  final2 <- buildFree @[g1|build|] $
    foldr (Free .: And . Free . Not . Free . State . Left) (Pure final1) [1..q2Next - 1]
  return (init1, final2, UnionQs qs2 qs1)
