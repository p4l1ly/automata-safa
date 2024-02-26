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
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Delit where

import Afa.Term as Term
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import Data.Traversable
import Control.Monad
import Data.Hashable
import qualified Data.HashSet as HS
import Afa.ShallowHashable

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

instance
  ( MonadFn0 (Explicit (MultiwayTerm q v r) r xBuild) m
  , MonadFn0 (Explicit r (MultiwayTerm q v r) xDeref) m
  , MonadFn0 (Explicit r Bool xIsTree) m
  , MonadFn0 (Explicit r r xShare) m
  , MonadFn0 (Explicit (r, MultiwayTerm q v r) r xReplace) m
  , Hashable (Shallow r)
  ) =>
  MonadFn0 (Explicit (MultiwayTerm q v r) r (Delit xBuild xDeref xIsTree xShare xReplace)) m
  where
  monadfn0 = \case
    fr@(NotMulti r) ->
      deref r >>= \case
        LTrueMulti -> build LFalseMulti
        LFalseMulti -> build LTrueMulti
        NotMulti r' -> do
          isTree r >>= \case
            True -> return r'
            False -> do
              r'' <- share r'
              replace (r, NotMulti r'')
              return r''
        _unmodifiedTerm -> build fr

    fr@(AndMulti (map unshallow . HS.toList -> xs)) -> do
      vals <- for xs deref
      if any (\case LFalseMulti -> True; _ok -> False) vals
        then build LFalseMulti
        else do
          let xsAndVals = [x | x@(_, val) <- zip xs vals, case val of LTrueMulti -> False; _ok -> True]
          if null xsAndVals
            then build LTrueMulti
            else do
              trees <- for xsAndVals (isTree . fst)
              let grandchildren = [ys | (AndMulti ys, True) <- zip vals trees]
              flattened <- case grandchildren of
                [] -> return $ Just HS.empty
                gs0:gss -> do
                  vals <- for gss $ mapM (deref . unshallow) . HS.toList
                  return $ foldM checkAndUnion gs0 $ zip vals gss
              let handled (AndMulti _) True = True
                  handled _ _ = False
              let freechildren =
                    [ ([val], HS.singleton (Shallow x))
                    | ((x, val), tr) <- zip xsAndVals trees
                    , not $ handled val tr
                    ]
              let flattened' = flattened >>= \fl -> foldM checkAndUnion fl freechildren
              case flattened' of
                Nothing -> build LFalseMulti
                Just xs' -> build $ AndMulti xs'

    fr@(OrMulti (map unshallow . HS.toList -> xs)) -> do
      vals <- for xs deref
      if any (\case LTrueMulti -> True; _ok -> False) vals
        then build LTrueMulti
        else do
          let xsAndVals = [x | x@(_, val) <- zip xs vals, case val of LFalseMulti -> False; _ok -> True]
          if null xsAndVals
            then build LFalseMulti
            else do
              trees <- for xsAndVals (isTree . fst)
              let grandchildren = [ys | (OrMulti ys, True) <- zip vals trees]
              flattened <- case grandchildren of
                [] -> return $ Just HS.empty
                gs0:gss -> do
                  vals <- for gss $ mapM (deref . unshallow) . HS.toList
                  return $ foldM checkAndUnion gs0 $ zip vals gss
              let handled (OrMulti _) True = True
                  handled _ _ = False
              let freechildren =
                    [ ([val], HS.singleton (Shallow x))
                    | ((x, val), tr) <- zip xsAndVals trees
                    , not $ handled val tr
                    ]
              let flattened' = flattened >>= \fl -> foldM checkAndUnion fl freechildren
              case flattened' of
                Nothing -> build LTrueMulti
                Just xs' -> build $ OrMulti xs'

    fr -> build fr
    where
      build = monadfn0 @(Explicit (MultiwayTerm q v r) r xBuild)
      deref = monadfn0 @(Explicit r (MultiwayTerm q v r) xDeref)
      isTree = monadfn0 @(Explicit r Bool xIsTree)
      share = monadfn0 @(Explicit r r xShare)
      replace = monadfn0 @(Explicit (r, MultiwayTerm q v r) r xReplace)

data DelitO (d :: * -> *) (cont :: *)
type instance
  Definition (DelitO d cont) =
    Name "build" (Delit [gc|build|] [gc|deref|] [gc|isTree|] [gc|share|] [gc|replace|])
      :+: Follow (d cont)

checkAndUnion ::
  ( Hashable (Shallow r)
  , Eq (Shallow r)
  )
  => HS.HashSet (Shallow r)
  -> ([MultiwayTerm q v r], HS.HashSet (Shallow r))
  -> Maybe (HS.HashSet (Shallow r))
checkAndUnion old (vals, new)
  | or [Shallow x `elem` old | (NotMulti x) <- vals] = Nothing
  | otherwise = Just $ HS.union new old
