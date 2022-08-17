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
{-# LANGUAGE MonadComprehensions #-}

module Afa.Convert.Smv2 where

import Afa.Finalful
import Afa.Finalful.STerm (Term (..), VarTra(..))
import Afa.IORef
import Afa.Lib (listArray')
import Afa.Negate (Qombo (Qombo))
import qualified Capnp.Gen.Afa.Model.Separated.Pure as AfaC
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Control.Lens (itraverse, (&))
import Control.Monad.State.Strict
import Control.Monad.Trans (lift)
import Data.Array
import Data.Char
import Data.Composition ((.:))
import Data.Foldable
import Data.Functor ((<&>))
import qualified Data.HashMap.Strict as HM
import Data.IORef
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo (..))
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Read as TR
import Data.Traversable
import Data.Word
import Debug.Trace
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Lift (Inc, K (K), LiftCount, Unwrap)
import Shaper
import Shaper.Helpers (BuildD, buildFree)
import TypeDict
import Control.Applicative
import Data.Maybe
import qualified Data.HashSet as S
import Data.Hashable

type FormatFormulaD d m =
  FormatFormulaD_ d m (FormatFormulaA d (Term [g|q|] [g|v|] [g|r|]) [g|r|]) [g|q|] [g|v|] [g|r|]
type FormatFormulaA (d :: TypeDict) x r =
  FormatFormulaA1
    ( Name "recur" (MkN (RecK r x T.Text) [d|any|])
        :+: Name "deref" (Mk (MfnK r (Term [g|q|] [g|v|] [g|r|])) [d|deref|])
        :+: End
    )
    r
type FormatFormulaA1 d' r =
  Name "isTree" (Mk IsTree [d'|recur|])
    :+: Name "rec" (Mk (MfnK r T.Text) [d'|recur|])
    :+: Name "self" (Mk (MfnK () r) [d'|recur|])
    :+: d'
type FormatFormulaD_ d (m :: * -> *) (d' :: TypeDict) (q :: *) (v :: *) (r :: *) =
  D.Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d' ~ FormatFormulaA d (Term q v r) r)
    :|: D.Name "show" (ShowT v, ShowT q)
    :|: D.Name "rec" (RecRecur [d'|recur|] m)
    :|: D.Name "deref" (MonadFn [d'|deref|] m)
    :|: D.End
formatFormula ::
  forall d q v r d'.
  D.ToConstraint (FormatFormulaD_ d IO d' q v r) =>
  IO (r -> IO T.Text, IO [(Int, T.Text)])
formatFormula = do
  let rec x = [d'|monadfn|rec|] x
  vFIx <- newIORef (0 :: Int)
  stack <- newIORef ([] :: [(Int, T.Text)])
  let algebra x = do
        [d'|ask|isTree|] >>= \case
          True ->
            case x of
              LTrue -> return "TRUE"
              LFalse -> return "FALSE"
              State q -> return $ T.cons 'q' (showT q)
              Var v -> return $ T.cons 'a' (showT v)
              Not !r -> do
                !r' <- rec r
                rt <- monadfn @(Inc [d'|deref|]) r
                case rt of
                  And _ _ -> return $ T.concat ["!(", r', ")"]
                  Or _ _ -> return $ T.concat ["!(", r', ")"]
                  _ -> return $ T.cons '!' r'
              And !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- monadfn @(Inc [d'|deref|]) a
                bt <- monadfn @(Inc [d'|deref|]) b
                let a'' = case at of
                      Or _ _ -> T.concat ["(", a', ")"]
                      _ -> a'
                let b'' = case bt of
                      Or _ _ -> T.concat ["(", b', ")"]
                      _ -> b'
                return $ T.concat [a'', " & ", b'']
              Or !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- monadfn @(Inc [d'|deref|]) a
                bt <- monadfn @(Inc [d'|deref|]) b
                let a'' = case at of
                      And _ _ -> T.concat ["(", a', ")"]
                      _ -> a'
                let b'' = case bt of
                      And _ _ -> T.concat ["(", b', ")"]
                      _ -> b'
                return $ T.concat [a'', " | ", b'']
          False -> do
            txt <- case x of
              LTrue -> return "TRUE"
              LFalse -> return "FALSE"
              State q -> return $ T.cons 'q' (showT q)
              Var v -> return $ T.cons 'a' (showT v)
              Not !r -> do
                !r' <- rec r
                rt <- monadfn @(Inc [d'|deref|]) r
                case rt of
                  And _ _ -> return $ T.concat ["!(", r', ")"]
                  Or _ _ -> return $ T.concat ["!(", r', ")"]
                  _ -> return $ T.cons '!' r'
              And !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- monadfn @(Inc [d'|deref|]) a
                bt <- monadfn @(Inc [d'|deref|]) b
                let a'' = case at of
                      Or _ _ -> T.concat ["(", a', ")"]
                      _ -> a'
                let b'' = case bt of
                      Or _ _ -> T.concat ["(", b', ")"]
                      _ -> b'
                return $ T.concat [a'', " & ", b'']
              Or !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- monadfn @(Inc [d'|deref|]) a
                bt <- monadfn @(Inc [d'|deref|]) b
                let a'' = case at of
                      And _ _ -> T.concat ["(", a', ")"]
                      _ -> a'
                let b'' = case bt of
                      And _ _ -> T.concat ["(", b', ")"]
                      _ -> b'
                return $ T.concat [a'', " | ", b'']
            fIx <- lift $ readIORef vFIx
            lift $ writeIORef vFIx $ fIx + 1
            lift $ modifyIORef stack ((fIx, txt) :)
            return $ do T.cons 'n' (T.pack (show fIx))

  convert <- recur @ [d'|recur|] algebra
  return (convert, readIORef stack)

unparen :: T.Text -> T.Text
unparen txt = 
  fromMaybe txt [txt'' | ('(', txt') <- T.uncons txt, (txt'', ')') <- T.unsnoc txt]

format ::
  forall d q v r d' allVars.
  ( D.ToConstraint (FormatFormulaD d IO)
  , q ~ [g|q|]
  , v ~ [g|v|]
  , r ~ [g|r|]
  , D.ToConstraint (SplitFinals'D d IO)
  , allVars ~ Mk (FRecK r r (VarTra IO v q v r)) [d|funr|]
  , FunRecur allVars IO
  , Eq v
  , Hashable v
  , ShowT v
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO ()
format init final (qCount, i2q, i2r, q2i) = do
  (convert, getShared) <- formatFormula @d

  -- TODO pure var list builder using VarFol?
  varsV <- newIORef S.empty
  loadVars <- funRecur @allVars $ VarTra \v ->
    Var v <$ modifyIORef varsV (S.insert v)
  loadVars init
  loadVars final
  for_ [0 .. qCount - 1] (loadVars . i2r)
  vars <- readIORef varsV

  TIO.putStrLn "MODULE main"
  TIO.putStrLn "VAR"
  for_ [0 .. qCount - 1] \qi -> TIO.putStrLn [i|  q#{showT $ i2q qi}: boolean;|]
  for_ vars \v -> TIO.putStrLn [i|  a#{showT v}: boolean;|]

  (finalnesses, _, complexFinals) <- splitFinals' @d final qCount q2i


  initF <- convert init
  complexFinals' <- for complexFinals convert
  qFs <- for [0 .. qCount - 1] (convert . i2r)

  TIO.putStrLn "DEFINE"
  getShared >>= mapM_ \(j, txt) -> TIO.putStrLn [i|  f#{j} := #{unparen txt};|]

  TIO.putStrLn "ASSIGN"
  for_ (zip [0..] qFs) \(qi, qF) -> do
    let qName = showT $ i2q qi
    case finalnesses ! qi of
      Final -> TIO.putStrLn [i|  init(q#{qName}) := TRUE;|]
      Nonfinal -> TIO.putStrLn [i|  init(q#{qName}) := FALSE;|]
      Complex -> return ()
    TIO.putStrLn [i|  next(q#{qName}) := #{unparen qF};|]

  for_ complexFinals' \f -> TIO.putStrLn [i|INIT #{unparen f}|]
  TIO.putStrLn [i|SPEC AG(!#{initF})|]

formatIORef ::
  forall q v r r' d result.
  ( r ~ Afa.IORef.Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , ShowT q
  , ShowT v
  , Eq v
  , Hashable v
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO ()
formatIORef = Afa.Convert.Smv2.format @d

class ShowT a where
  showT :: a -> T.Text

instance ShowT T.Text where
  showT = id

instance ShowT q => ShowT (SyncQs q) where
  showT (QState q) = [i|Q#{showT q}|]
  showT SyncState = "Sync"

instance (ShowT q, ShowT v) => ShowT (SyncVar q v) where
  showT (VVar v) = [i|V#{showT v}|]
  showT (QVar v) = [i|Q#{showT v}|]
  showT FVar = "F"

instance ShowT q => ShowT (Qombo q) where
  showT (Qombo n q) = [i|C#{n}_#{showT q}|]
