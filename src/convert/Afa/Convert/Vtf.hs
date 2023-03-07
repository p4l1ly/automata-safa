{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=5 #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Convert.Vtf where

import Afa.Build
import Afa.States
import Afa.Term (Term (..), q, r, v)
import Control.Monad.Writer
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import Data.Traversable
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import Data.Composition
import Data.Fix

data VtfStatement
  = Initial [T.Text]
  | Final [T.Text]
  | Transition (T.Text, T.Text, T.Text)

parseStatements :: T.Text -> [VtfStatement]
parseStatements = mapMaybe parseLine . T.lines

parseLine :: T.Text -> Maybe VtfStatement
parseLine t
  | t == "" = Nothing
  | t == "@NFA" = Nothing
parseLine (T.stripPrefix "%States " -> Just qs) = Nothing
parseLine (T.stripPrefix "%Initial " -> Just qs) = Just $ Initial (T.words qs)
parseLine (T.stripPrefix "%Final " -> Just qs) = Just $ Final (T.words qs)
parseLine (T.words -> [q1, a, q2]) = Just $ Transition (q1, a, q2)
parseLine _ = Nothing

groupDefs ::
  [VtfStatement] ->
  ( [T.Text]
  , [T.Text]
  , HM.HashMap T.Text [(T.Text, T.Text)]
  )
groupDefs defs =
  ( case appEndo init [] of [x] -> x; _ -> error "expected single kInitialFormula"
  , case appEndo final [] of [x] -> x; _ -> error "expected single kFinalFormula"
  , ($ []) <$> HM.fromListWith (.) (appEndo states [])
  )
  where
    (init, final, states) = execWriter $
      for defs $ \case
        Initial qs -> tell (Endo (qs :), mempty, mempty)
        Final qs -> tell (mempty, Endo (qs :), mempty)
        Transition (q1, a, q2) -> tell (mempty, mempty, Endo ((q1, ((a, q2) :)) :))

type ParseD d = ParseI d (ParseA d)

data ParseA d
type instance
  Definition (ParseA d) =
    Name "build" (Inherit (Explicit [g|term|] $r) [k|build|])
      :+: End

type ParseI d d1 =
  ( d1 ~ ParseA d
  , Term T.Text T.Text $r ~ [g|term|]
  , MonadFn [g1|build|] IO
  )

type Qs r = StateHashMap T.Text r

parse ::
  forall d d1.
  ParseI d d1 =>
  [VtfStatement] ->
  IO ($r, $r, StateHashMap T.Text [($r, $r)])
parse (groupDefs -> (inits, finals, states)) = do
  -- allStates only finds each state occurence and adds it into the HashSet
  let allStates = foldr (flip (foldr (HS.insert . snd))) (foldr HS.insert (HS.fromMap $ void states) inits) states
  init' <- buildFix @[g1|build|] $ foldr (Fix .: Or . Fix . State) (Fix LFalse) inits
  final' <- buildFix @[g1|build|] $ foldr (Fix .: And . Fix . Not . Fix . State) (Fix LTrue) $
    foldr HS.delete allStates finals
  states' <- fmap StateHashMap $ for states $ mapM \(a, q) ->
    (,) <$> monadfn @[g1|build|] (Var a) <*> monadfn @[g1|build|] (State q)
  return (init', final', states')
