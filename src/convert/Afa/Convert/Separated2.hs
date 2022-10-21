{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Convert.Separated2 where

import Afa.Finalful
import Afa.Finalful.STerm (Term (..), VarTra (..))
import Afa.IORef
import Afa.Lib (listArray')
import Afa.Negate (Qombo (Qombo))
import qualified Capnp
import qualified Capnp.Gen.Afa.Model.Separated as AfaC
import qualified Capnp.Gen.Afa.Model.Term as TermC
import Control.Applicative
import Control.Arrow ((>>>))
import Control.Lens (itraverse, (&))
import Control.Monad.State.Strict
import Control.Monad.Trans (lift)
import Data.Array
import Data.Char
import Data.Composition ((.:))
import Data.Foldable
import Data.Functor ((<&>))
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as S
import Data.Hashable
import Data.IORef
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe
import Data.Monoid (Endo (..))
import Data.String.Interpolate.IsString (i)
import Data.Traversable
import qualified Data.Vector as V
import Data.Word
import Debug.Trace
import Shaper
import Shaper.Helpers (BuildD, buildFree)
import System.IO
import InversionOfControl.TypeDict
import InversionOfControl.Lift

type FormatFormulaD d m =
  FormatFormulaD_ d m (FormatFormulaA d (Term Int Int [g|r|]) [g|r|]) [g|r|]
type FormatFormulaA (d :: TypeDict) x r =
  FormatFormulaA1
    ( Name "recur" (MkN (RecK r x Word32) [d|any|])
        :+: Name "deref" (Mk (MfnK r (Term Int Int [g|r|])) [d|deref|])
        :+: End
    )
    r
type FormatFormulaA1 d' r =
  Name "rec" (Mk (MfnK r Word32) [d'|recur|])
    :+: Name "self" (Mk (MfnK () r) [d'|recur|])
    :+: d'
type FormatFormulaD_ d (m :: * -> *) (d' :: TypeDict) (r :: *) =
  Name "aliases" (Int ~ [g|q|], Int ~ [g|v|], r ~ [g|r|], d' ~ FormatFormulaA d (Term Int Int r) r)
    :+: Name "rec" (RecRecur [d'|recur|] m)
    :+: Name "deref" (MonadFn [d'|deref|] m)
    :+: End

formatQFormula ::
  forall d r d'.
  ToConstraint (FormatFormulaD_ d IO d' r) =>
  IO
    ( r -> IO Word32
    , IORef [Capnp.Parsed TermC.QTerm11]
    )
formatQFormula = do
  let rec x = [d'|monadfn|rec|] x
  fIxV <- newIORef (0 :: Word32)
  shareds <- newIORef ([] :: [Capnp.Parsed TermC.QTerm11])

  let algebra x = do
        term <- contents
        fIx <- lift $ readIORef fIxV
        lift $ writeIORef fIxV $ fIx + 1
        lift $ modifyIORef shareds (term :)
        return fIx
        where
          contents =
            (\x -> TermC.QTerm11{union' = x})
              <$> case x of
                LTrue -> return TermC.QTerm11'litTrue
                LFalse -> error "LFalse in qFormula"
                State q -> return $ TermC.QTerm11'state (fromIntegral q)
                Var v -> error "Var in qFormula"
                Not !r -> error "Not in qFormula"
                And !a !b -> do
                  !a' <- rec a
                  !b' <- rec b
                  return $ TermC.QTerm11'and (V.fromList [a', b'])
                Or !a !b -> do
                  !a' <- rec a
                  !b' <- rec b
                  return $ TermC.QTerm11'or (V.fromList [a', b'])

  convert <- recur @[d'|recur|] algebra
  return (convert, shareds)

formatAFormula ::
  forall d r d'.
  ToConstraint (FormatFormulaD_ d IO d' r) =>
  IO
    ( r -> IO Word32
    , IORef [Capnp.Parsed TermC.BoolTerm11]
    )
formatAFormula = do
  let rec x = [d'|monadfn|rec|] x
  fIxV <- newIORef (0 :: Word32)
  shareds <- newIORef ([] :: [Capnp.Parsed TermC.BoolTerm11])

  let algebra x = do
        term <- contents
        fIx <- lift $ readIORef fIxV
        lift $ writeIORef fIxV $ fIx + 1
        lift $ modifyIORef shareds (term :)
        return fIx
        where
          contents =
            (\x -> TermC.BoolTerm11{union' = x})
              <$> case x of
                LTrue -> return TermC.BoolTerm11'litTrue
                LFalse -> return TermC.BoolTerm11'litFalse
                State q -> error "State in aFormula"
                Var v -> return $ TermC.BoolTerm11'predicate (fromIntegral v)
                Not !r -> do
                  !r' <- rec r
                  return $ TermC.BoolTerm11'not r'
                And !a !b -> do
                  !a' <- rec a
                  !b' <- rec b
                  return $ TermC.BoolTerm11'and (V.fromList [a', b'])
                Or !a !b -> do
                  !a' <- rec a
                  !b' <- rec b
                  return $ TermC.BoolTerm11'or (V.fromList [a', b'])

  convert <- recur @[d'|recur|] algebra
  return (convert, shareds)

format ::
  forall d r d' allVars.
  ( ToConstraint (FormatFormulaD d IO)
  , r ~ [g|r|]
  , ToConstraint (SplitFinals'D d IO)
  , allVars ~ Mk (FRecK r r (VarTra IO Int Int Int r)) [d|funr|]
  , FunRecur allVars IO
  ) =>
  r ->
  r ->
  (Int, Int -> Int, Int -> [(r, r)], Int -> Int) ->
  IO ()
format init final (qCount, i2q, i2r, q2i) = do
  (qConvert, qSharedsV) <- formatQFormula @d
  (aConvert, aSharedsV) <- formatAFormula @d

  -- TODO pure var list builder using VarFol?
  varCountV <- newIORef (-1)
  loadVars <- funRecur @allVars $ VarTra \v ->
    Var v <$ modifyIORef varCountV (max v)
  loadVars init
  loadVars final
  for_ [0 .. qCount - 1] $ mapM_ (loadVars . fst) . i2r
  varCount <- readIORef varCountV

  initF <- qConvert init

  (finalnesses, _, Nothing) <- splitFinals' @d final qCount q2i
  let finalStates = filter (\i -> finalnesses ! i == Final) [0 .. qCount - 1]

  qFs <- for [0 .. qCount - 1] \qi -> do
    transitions' <- for (i2r qi) \(aGuard, qSucc) -> do
      qSucc' <- qConvert qSucc
      aGuard' <- aConvert aGuard
      return $ AfaC.SimpleConjunct11 aGuard' qSucc'
    return $ V.fromList transitions'

  qterms <- readIORef qSharedsV
  aterms <- readIORef aSharedsV

  Capnp.hPutParsed stdout $
    AfaC.BoolAfa2
      { AfaC.aterms = V.reverse $ V.fromList aterms
      , AfaC.qterms = V.reverse $ V.fromList qterms
      , AfaC.states = V.fromList qFs
      , AfaC.varCount = fromIntegral (varCount + 1)
      , AfaC.initialFormula = initF
      , AfaC.finalStates = V.fromList $ map fromIntegral finalStates
      }

formatIORef ::
  forall r r' d result.
  ( r ~ Afa.IORef.Ref (Term Int Int)
  , d ~ IORefRemoveFinalsD Int Int r r'
  ) =>
  r ->
  r ->
  (Int, Int -> Int, Int -> [(r, r)], Int -> Int) ->
  IO ()
formatIORef = Afa.Convert.Separated2.format @d

twoFormat ::
  forall d r d' allVars.
  ( ToConstraint (FormatFormulaD d IO)
  , r ~ [g|r|]
  , ToConstraint (SplitFinals'D d IO)
  , allVars ~ Mk (FRecK r r (VarTra IO Int Int Int r)) [d|funr|]
  , FunRecur allVars IO
  ) =>
  r ->
  r ->
  r ->
  r ->
  (Int, Int -> Int, Int -> [(r, r)], Int -> Int) ->
  IO ()
twoFormat init1 final1 init2 final2 (qCount, i2q, i2r, q2i) = do
  (qConvert, qSharedsV) <- formatQFormula @d
  (aConvert, aSharedsV) <- formatAFormula @d

  -- TODO pure var list builder using VarFol?
  varCountV <- newIORef (-1)
  loadVars <- funRecur @allVars $ VarTra \v ->
    Var v <$ modifyIORef varCountV (max v)
  loadVars init1
  loadVars final1
  loadVars init2
  loadVars final2
  for_ [0 .. qCount - 1] $ mapM_ (loadVars . fst) . i2r
  varCount <- readIORef varCountV

  initF1 <- qConvert init1
  initF2 <- qConvert init2

  (finalnesses1, _, Nothing) <- splitFinals' @d final1 qCount q2i
  let finalStates1 = filter (\i -> finalnesses1 ! i == Final) [0 .. qCount - 1]
  (finalnesses2, _, Nothing) <- splitFinals' @d final2 qCount q2i
  let finalStates2 = filter (\i -> finalnesses2 ! i == Final) [0 .. qCount - 1]

  qFs <- for [0 .. qCount - 1] \qi -> do
    transitions' <- for (i2r qi) \(aGuard, qSucc) -> do
      qSucc' <- qConvert qSucc
      aGuard' <- aConvert aGuard
      return $ AfaC.SimpleConjunct11 aGuard' qSucc'
    return $ V.fromList transitions'

  qterms <- readIORef qSharedsV
  aterms <- readIORef aSharedsV

  Capnp.hPutParsed stdout $
    AfaC.TwoBoolAfas
      { AfaC.aterms = V.reverse $ V.fromList aterms
      , AfaC.qterms = V.reverse $ V.fromList qterms
      , AfaC.states = V.fromList qFs
      , AfaC.varCount = fromIntegral (varCount + 1)
      , AfaC.initialFormula1 = initF1
      , AfaC.initialFormula2 = initF2
      , AfaC.finalStates1 = V.fromList $ map fromIntegral finalStates1
      , AfaC.finalStates2 = V.fromList $ map fromIntegral finalStates2
      }

twoFormatIORef ::
  forall r r' d result.
  ( r ~ Afa.IORef.Ref (Term Int Int)
  , d ~ IORefRemoveFinalsD Int Int r r'
  ) =>
  r ->
  r ->
  r ->
  r ->
  (Int, Int -> Int, Int -> [(r, r)], Int -> Int) ->
  IO ()
twoFormatIORef = Afa.Convert.Separated2.twoFormat @d
