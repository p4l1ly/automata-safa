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

module Afa.Convert.Ada2 where

import Afa.Finalful
import Afa.Finalful.STerm (Term (..))
import Afa.IORef
import Afa.Lib (listArray')
import Afa.Negate (Qombo (Qombo))
import qualified Capnp.Gen.Afa.Model.Separated as AfaC
import Control.Applicative
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
import Data.Maybe
import Data.Monoid (Endo (..))
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Text.Read as TR
import Data.Traversable
import qualified Data.Vector as V
import Data.Word
import Debug.Trace
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Lift (Inc, K (K), LiftCount, Unwrap)
import Shaper
import Shaper.Helpers (BuildD, buildFree)
import TypeDict

type V = AfaC.Parsed AfaC.Range16
type FormatFormulaD d m =
  FormatFormulaD_ d m (FormatFormulaA d (Term [g|q|] V [g|r|]) [g|r|]) [g|q|] [g|r|]
type FormatFormulaA (d :: TypeDict) x r =
  FormatFormulaA1
    ( Name "recur" (MkN (RecK r x T.Text) [d|any|])
        :+: Name "deref" (Mk (MfnK r (Term [g|q|] V [g|r|])) [d|deref|])
        :+: End
    )
    r
type FormatFormulaA1 d' r =
  Name "rec" (Mk (MfnK r T.Text) [d'|recur|])
    :+: d'
type FormatFormulaD_ d (m :: * -> *) (d' :: TypeDict) (q :: *) (r :: *) =
  D.Name "aliases" (q ~ [g|q|], V ~ [g|v|], r ~ [g|r|], d' ~ FormatFormulaA d (Term q V r) r)
    :|: D.Name "show" (ShowT q)
    :|: D.Name "rec" (RecRecur [d'|recur|] m)
    :|: D.Name "deref" (MonadFn [d'|deref|] m)
    :|: D.End
formatFormula ::
  forall d q r d'.
  D.ToConstraint (FormatFormulaD_ d IO d' q r) =>
  IO (r -> IO T.Text)
formatFormula = do
  let rec x = [d'|monadfn|rec|] x
  let algebra x =
        case x of
          LTrue -> return "true"
          LFalse -> return "false"
          State q -> return $ T.cons 'q' (showT q)
          Var (AfaC.Range16 0x0000 0xffff) -> return "true"
          Var (AfaC.Range16 0x0000 end) -> return [i|(<= v1 #{end})|]
          Var (AfaC.Range16 begin 0xffff) -> return [i|(>= v1 #{begin})|]
          Var (AfaC.Range16 begin end)
            | begin > end -> return "false"
            | begin == end -> return [i|(= v1 #{begin})|]
            | otherwise -> return [i|(and (>= v1 #{begin}) (<= v1 #{end}))|]
          Not !r -> do
            !r' <- rec r
            return $ T.concat ["(not ", r', ")"]
          And !a !b -> do
            !a' <- rec a
            !b' <- rec b
            let a''
                  | "(and " `T.isPrefixOf` a' = T.drop 5 $ T.take (T.length a' - 1) a'
                  | otherwise = a'
            let b''
                  | "(and " `T.isPrefixOf` b' = T.drop 5 $ T.take (T.length b' - 1) b'
                  | otherwise = b'
            return $ T.concat ["(and ", a'', " ", b'', ")"]
          Or !a !b -> do
            !a' <- rec a
            !b' <- rec b
            let a''
                  | "(or " `T.isPrefixOf` a' = T.drop 4 $ T.take (T.length a' - 1) a'
                  | otherwise = a'
            let b''
                  | "(or " `T.isPrefixOf` b' = T.drop 4 $ T.take (T.length b' - 1) b'
                  | otherwise = b'
            return $ T.concat ["(or ", a'', " ", b'', ")"]

  recur @[d'|recur|] algebra

class ShowT a where
  showT :: a -> T.Text

instance ShowT T.Text where
  showT = id

instance ShowT Word32 where
  showT = T.pack . show

instance ShowT Word8 where
  showT = T.pack . show

instance ShowT q => ShowT (SyncQs q) where
  showT (QState q) = [i|Q#{showT q}|]
  showT SyncState = "Sync"

instance (ShowT q, ShowT v) => ShowT (SyncVar q v) where
  showT (VVar v) = [i|V#{showT v}|]
  showT (QVar v) = [i|Q#{showT v}|]
  showT FVar = "F"

instance ShowT q => ShowT (Qombo q) where
  showT (Qombo n q) = [i|C#{n}_#{showT q}|]

formatSeparated ::
  forall d deref.
  ( D.ToConstraint (FormatFormulaD d IO)
  , deref ~ Mk (MfnK [g|r|] (Term [g|q|] [g|v|] [g|r|])) [d|deref|]
  , MonadFn deref IO
  ) =>
  [g|r|] ->
  [[g|q|]] ->
  (Int, Int -> [g|q|], Int -> V.Vector ([g|r|], [g|r|]), [g|q|] -> Int) ->
  IO ()
formatSeparated init finals (qCount, i2q, i2r, q2i) = do
  let showState q = [i|q#{showT q}|]

  convert <- formatFormula @d

  TIO.putStrLn "STATES"
  if qCount == 0
    then TIO.putStrLn "q"
    else TIO.putStrLn $ T.unwords $ map (showState . i2q) [0 .. qCount - 1]
  TIO.putStrLn ""

  TIO.putStrLn "INITIAL"
  TIO.putStrLn =<< convert init
  TIO.putStrLn ""

  TIO.putStrLn "FINAL"
  TIO.putStrLn $ T.unwords $ map showState finals
  TIO.putStrLn ""

  TIO.putStrLn "SYMBOLS"
  TIO.putStrLn "a"
  TIO.putStrLn ""

  TIO.putStrLn "VARIABLES"
  TIO.putStrLn "v"
  TIO.putStrLn ""

  let printGuardAndSucc (aterm, qterm) = do
        aterm' <- monadfn @deref aterm
        qterm' <- monadfn @deref qterm
        case (aterm', qterm') of
          (LFalse, _) -> TIO.putStr "false"
          (_, LFalse) -> TIO.putStr "false"
          (LTrue, _) -> TIO.putStr =<< convert qterm
          (_, LTrue) -> TIO.putStr =<< convert aterm
          _ -> do
            TIO.putStr "(and "
            TIO.putStr =<< convert aterm
            TIO.putStr " "
            TIO.putStr =<< convert qterm
            TIO.putStr ")"

  TIO.putStrLn "TRANSITIONS"
  for_ [0 .. qCount - 1] \qi -> do
    TIO.putStrLn [i|a q#{showT $ i2q qi}|]
    let transitions = i2r qi
    case V.length transitions of
      0 -> TIO.putStr "false"
      1 -> printGuardAndSucc (transitions V.! 0)
      _ -> do
        TIO.putStr "(or"
        for_ transitions \t -> do
          TIO.putStr " "
          printGuardAndSucc t
        TIO.putStr ")"
    TIO.putStrLn "\n#"

formatSeparatedIORef ::
  forall q r r' d result.
  ( r ~ Afa.IORef.Ref (Term q V)
  , d ~ IORefRemoveFinalsD q V r r'
  , ShowT q
  ) =>
  r ->
  [q] ->
  (Int, Int -> q, Int -> V.Vector (r, r), q -> Int) ->
  IO ()
formatSeparatedIORef = Afa.Convert.Ada2.formatSeparated @d

format ::
  forall d deref.
  ( D.ToConstraint (FormatFormulaD d IO)
  , deref ~ Mk (MfnK [g|r|] (Term [g|q|] [g|v|] [g|r|])) [d|deref|]
  , MonadFn deref IO
  ) =>
  [g|r|] ->
  [[g|q|]] ->
  (Int, Int -> [g|q|], Int -> [g|r|], [g|q|] -> Int) ->
  IO ()
format init finals (qCount, i2q, i2r, q2i) = do
  let showState q = [i|q#{showT q}|]

  convert <- formatFormula @d

  TIO.putStrLn "STATES"
  if qCount == 0
    then TIO.putStrLn "q"
    else TIO.putStrLn $ T.unwords $ map (showState . i2q) [0 .. qCount - 1]
  TIO.putStrLn ""

  TIO.putStrLn "INITIAL"
  TIO.putStrLn =<< convert init
  TIO.putStrLn ""

  TIO.putStrLn "FINAL"
  TIO.putStrLn $ T.unwords $ map showState finals
  TIO.putStrLn ""

  TIO.putStrLn "SYMBOLS"
  TIO.putStrLn "a"
  TIO.putStrLn ""

  TIO.putStrLn "VARIABLES"
  TIO.putStrLn "v"
  TIO.putStrLn ""

  let printGuardAndSucc (aterm, qterm) = do
        aterm' <- monadfn @deref aterm
        qterm' <- monadfn @deref qterm
        case (aterm', qterm') of
          (LFalse, _) -> TIO.putStr "false"
          (_, LFalse) -> TIO.putStr "false"
          (LTrue, _) -> TIO.putStr =<< convert qterm
          (_, LTrue) -> TIO.putStr =<< convert aterm
          _ -> do
            TIO.putStr "(and "
            TIO.putStr =<< convert aterm
            TIO.putStr " "
            TIO.putStr =<< convert qterm
            TIO.putStr ")"

  TIO.putStrLn "TRANSITIONS"
  for_ [0 .. qCount - 1] \qi -> do
    TIO.putStrLn [i|a q#{showT $ i2q qi}|]
    TIO.putStrLn =<< convert (i2r qi)
    TIO.putStrLn "#"

formatIORef ::
  forall q r r' d result.
  ( r ~ Afa.IORef.Ref (Term q V)
  , d ~ IORefRemoveFinalsD q V r r'
  , ShowT q
  ) =>
  r ->
  [q] ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO ()
formatIORef = Afa.Convert.Ada2.format @d
