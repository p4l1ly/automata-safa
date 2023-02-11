{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

module Afa.RemoveFinals where

import Afa.Build
import Afa.States hiding (Q, R)
import Afa.Term
import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans
import Data.Array
import Data.Bifunctor
import Data.Fix
import Data.Function.Apply
import Data.Function.Syntax ((.:))
import Data.Functor
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Hashable
import Data.Kind
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Traversable
import InversionOfControl.Lift
import qualified InversionOfControl.MapRecur as MR
import InversionOfControl.MonadFn
import qualified InversionOfControl.Recur as R
import InversionOfControl.TypeDict
import qualified Afa.Lib as Lib
import Data.Foldable
import Control.Monad.Identity
import Control.Lens ((&))

data SyncVar q v = VVar v | FVar | QVar q deriving (Eq, Show)
data Finalness = Final | Complex | Nonfinal deriving (Eq, Show, Ord)

data RemoveFinalsO d
type instance Definition (RemoveFinalsO d) =
  Name "term" (GetF "term'" (RemoveFinalsA d Identity))
    :+: Name "qs" (Lib.AddOneQs (RTraversed $qs $rSelf))
    :+: Follow d

data RemoveFinalsA d (m :: * -> *)
type instance Definition (RemoveFinalsA d m) =
  Name "mapF" (($q -> Lib.AddOneQ $q) :&: ($v -> SyncVar $q $v))
    :+: Name "r'" (Creation ([g|mapRecFunR'|] $r '[Q, V]) [gs|mapF|])
    :+: Name "term'" (Term (Lib.AddOneQ $q) (SyncVar $q $v) [gs|r'|])
    :+: Name "mapK" ([g|mapRecFun|] '[Q, V] :: *)
    :+: Name "map" (MR.Explicit [k|mapRec|] $r [gs|r'|] (Creation [gs|mapK|] [gs|mapF|]))
    :+: Name "qs'" (RTraversed $qs [gs|r'|])
    :+: Name "recBuildFF" (R.Explicit [k|rcata|] Zero [gs|r'|] ([gs|r'|], [gs|term'|]))
    :+: Name "share" (Inherit (Explicit [gs|r'|] [gs|r'|]) [k|share|])
    :+: Name "build" (Inherit (Explicit [gs|term'|] [gs|r'|]) [k|build|])
    :+: Name "deref" (Inherit (Explicit [gs|r'|] [gs|term'|]) [k|deref|])
    :+: Name "mapF2" ([gs|r'|] -> MR.Et [gs|map|] m [gs|r'|])
    :+: Name "mapK2" ([g|mapRecTra|] '[R] :: *)
    :+: Name "map2" (MR.Explicit (Inc [k|mapRec|]) [gs|r'|] [gs|r'|] (Creation [gs|mapK2|] [gs|mapF2|]))
    :+: End

type RemoveFinalsI d d1 m =
  ( d1 ~ RemoveFinalsA d m
  , Create [g1|mapK|] [g1|mapF|]
  , MR.Recur [g1|map|] m
  , RTraversable $qs $q $r [g1|r'|] [g1|qs'|]
  , RTraversable (GetF "qs'" (SplitFinalsA d)) $q Finalness [g1|r'|] [g1|qs'|]
  , SplitFinalsD d m
  , R.Recur [g1|recBuildFF|] [g1|r'|] m
  , BuildFinalConstraintD d m
  , Create [g1|mapK2|] [g1|mapF2|]
  , MR.Recur [g1|map2|] (MR.Et [g1|map|] m)
  , MonadFn [g1|deref|] m
  , MonadFn [g1|build|] m
  , MonadFn [g1|share|] m
  )

removeFinals ::
  forall d m d1.
  RemoveFinalsI d d1 m =>
  ($r, $r, $qs) -> m ([g1|r'|], Lib.AddOneQs [g1|qs'|])
removeFinals (init, final, qs) = do
  (finalnesses, complex) <- splitFinals @d final qs

  let mfun = create @[g1|mapK|] (Lib.OriginalQ :&: VVar :: [g1|mapF|])
  MR.runRecur @[g1|map|] mfun \changeAlphabet ->
    if all (\(_, fin) -> fin == Nonfinal) $ stateList finalnesses
      then do
        init' <- changeAlphabet init
        qs' <- traverseR changeAlphabet qs
        ltrue <- lift $ monadfn @[g1|build|] LTrue
        return (init', Lib.AddOneQs qs' ltrue)
      else do
        finalConstraint <- case complex of
          Nothing -> return Nothing
          Just complex -> do
            complex' <- changeAlphabet complex
            Just <$> lift do
              R.runRecur @[g1|recBuildFF|]
                (buildFinalConstraint @(LiftUp d))
                ($ complex')

        -- build a corresponding term t_q for each state;
        qsubs <-
          lift $ finalnesses & traverseQR \q ->
            \case
              Final ->
                monadfn @[g1|share|] =<< buildFix @[g1|build|]
                  (Fix $ Or (Fix $ State $ Lib.OriginalQ q) (Fix $ Var FVar))
              Complex -> do
                monadfn @[g1|share|] =<< buildFix @[g1|build|]
                  ( (Fix .: Or)
                      (Fix $ And (Fix $ Not (Fix $ Var FVar)) (Fix $ State $ Lib.OriginalQ q))
                      (Fix $ And (Fix $ Var FVar) (Fix $ Var $ QVar q))
                  )
              Nonfinal ->
                monadfn @[g1|share|] =<< buildFix @[g1|build|]
                  (Fix $ And (Fix $ State $ Lib.OriginalQ q) (Fix $ Not $ Fix $ Var FVar))

        let redirectFn r =
              lift $ monadfn @[g1|deref|] r <&> \case
                State (Lib.OriginalQ q) -> transition qsubs q
                _ -> r
        let mtra = create @[g1|mapK2|] (redirectFn :: [g1|mapF2|])
        MR.runRecur @[g1|map2|] mtra \redirect -> do
          qs' <- traverseR (redirect <=< lift . changeAlphabet) qs
          init' <- redirect =<< lift (changeAlphabet init)
          lift $ lift $ case finalConstraint of
            Nothing -> do
              ltrue <- monadfn @[g1|build|] LTrue
              return (init', Lib.AddOneQs qs' ltrue)
            Just finalConstraint -> do
              syncQRef <- monadfn @[g1|build|] (State Lib.AddedQ) >>= monadfn @[g1|share|]
              syncQTrans <- buildFree @[g1|build|] $
                (Free .: Or)
                  (Free $ And (Free $ Not (Free $ Var FVar)) (Pure syncQRef))
                  (Free $ And (Free $ Var FVar) (Pure finalConstraint))
              init'' <- monadfn @[g1|build|] (And syncQRef init')
              return (init'', Lib.AddOneQs qs' syncQTrans)

type BuildFinalConstraintI d m d1 d2 =
  ( d1 ~ RemoveFinalsO d
  , d2 ~ BuildShareSharedTermO d1
  , BuildShareSharedD d2 m
  )

type BuildFinalConstraintD d m =
  BuildFinalConstraintI d m (RemoveFinalsO d) (BuildShareSharedTermO (RemoveFinalsO d))

buildFinalConstraint ::
  forall d m d1 d2.
  BuildFinalConstraintI d m d1 d2 =>
  ($r1 -> m $r1) ->
  ($r1, [g1|term|]) ->
  m $r1
buildFinalConstraint rec (r0, term) = case term of
  (State (Lib.OriginalQ q)) -> buildShareShared @d2 r0 $ Var (QVar q)
  (And a b) -> buildShareShared @d2 r0 =<< And <$> rec a <*> rec b
  (Or a b) -> buildShareShared @d2 r0 =<< Or <$> rec a <*> rec b
  (Not a) -> buildShareShared @d2 r0 . Not =<< rec a
  _ -> return r0


data SplitFinalsA d
type instance Definition (SplitFinalsA d) =
  Name "rec" (R.Explicit [k|cata|] Zero $r [g|term|])
    :+: Name "qs'" (RTraversed $qs Finalness)
    :+: End

type SplitFinalsI d d1 m =
  ( d1 ~ SplitFinalsA d
  , R.Recur [g1|rec|] (Endo [$q]) m
  , Lib.SplitFinalsD d m
  , RTraversable $qs $q $r Finalness [g1|qs'|]
  , States [g1|qs'|] $q Finalness
  )

type SplitFinalsD d m = SplitFinalsI d (SplitFinalsA d) m

splitFinals ::
  forall d d1 m.
  SplitFinalsI d d1 m =>
  $r -> $qs -> m ([g1|qs'|], Maybe $r)
splitFinals final qs = do
  (nonfinals, complex) <- Lib.splitFinals @d final
  ((`appEndo` []) -> complexFinals) <- case complex of
    Nothing -> return mempty
    Just complex -> R.runRecur @[g1|rec|] findQsAlg ($ final)

  let qs1 = runIdentity $ traverseR (const $ Identity Final) qs
  let qs2 = redirect qs1 $
        map (, Complex) complexFinals
        ++ map (, Nonfinal) nonfinals

  return (qs2, complex)
  where
    findQsAlg rec = \case
      State q -> return $ Endo (q:)
      term -> fold <$> mapM rec term
