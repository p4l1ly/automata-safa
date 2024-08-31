{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Convert.Qcir where

import Afa.Convert.Identifier
import Afa.Term (Term (..), MultiwayTerm (..), q, r, v)
import Control.Applicative
import Control.Monad.Free
import Control.Monad.Writer
import Data.Attoparsec.Expr
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
import Data.Char
import Data.Composition
import Data.Foldable
import Data.Functor
import qualified Data.HashMap.Strict as HM
import Data.IORef
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Traversable
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import qualified InversionOfControl.Recur as R
import InversionOfControl.TypeDict
import Afa.States
import Afa.Build
import System.IO (Handle, stdout)
import qualified System.IO
import Data.Kind
import qualified Data.HashSet as HS
import Afa.ShallowHashable
import qualified Afa.Lib

type FormatFormulaD d = FormatFormulaI d (FormatFormulaA d $r)

data FormatFormulaA d r
type instance Definition (FormatFormulaA d r) =
  Name "deref" (Inherit (Explicit r [g|term|]) [k|deref|])
    :+: Name "isTree" (Inherit (Explicit r Bool) [k|isTree|])
    :+: Name "rec" (R.Explicit [k|rcata|] Zero r (r, [g|term|]))
    :+: End

type FormatFormulaI d d1 =
  ( d1 ~ FormatFormulaA d $r
  , MultiwayTerm $q $v $r ~ [g|term|]
  , Identify $q
  , Identify $v
  , MonadFn [g1|deref|] IO
  , MonadFn [g1|isTree|] IO
  , R.Recur [g1|rec|] T.Text IO
  ) :: Constraint

formatFormula ::
  forall d d1 t a.
  ( FormatFormulaI d d1
  , t ~ R.Et [g1|rec|]
  ) =>
  IO
    ( (($r -> t IO T.Text) -> t IO a) -> IO a
    , IO ([(Int, T.Text)], Bool, Bool)
    )
formatFormula = do
  vFIx <- newIORef (0 :: Int)
  stack <- newIORef ([] :: [(Int, T.Text)])
  hasTrue <- newIORef False
  hasFalse <- newIORef False

  let algebra :: ($r -> t IO T.Text) -> ($r, [g|term|]) -> t IO T.Text
      algebra rec (r, fr) = do
        lift (monadfn @[g1|deref|] r) >>= \case
          LTrueMulti -> do
            lift $ writeIORef hasTrue True
            return "fTrue"
          LFalseMulti -> do
            lift $ writeIORef hasFalse True
            return "fFalse"
          NotMulti !r -> T.cons '-' <$> rec r
          StateMulti q -> return $ T.append "l1_" (identify q)
          VarMulti v -> return $ T.cons 'a' (identify v)
          fr -> do
            txt <- case fr of
              AndMulti (map unshallow . HS.toList -> xs) -> do
                !xs' <- mapM rec xs
                return $ T.concat ["and(", T.intercalate ", " xs', ")"]
              OrMulti (map unshallow . HS.toList -> xs) -> do
                !xs' <- mapM rec xs
                return $ T.concat ["or(", T.intercalate ", " xs', ")"]

            fIx <- lift $ readIORef vFIx
            lift $ writeIORef vFIx $ fIx + 1
            lift $ modifyIORef stack ((fIx, txt) :)
            return $ do T.cons 'f' (T.pack (show fIx))

  return
    ( R.runRecur @[g1|rec|] algebra
    , (,,) <$> readIORef stack <*> readIORef hasTrue <*> readIORef hasFalse
    )

type PrintD d = PrintI d (PrintA d)

data PrintA d
type instance Definition (PrintA d) =
  Name "deref" (Inherit (Explicit $r [g|term|]) [k|deref|])
    :+: End

type PrintI d d1 =
  ( d1 ~ PrintA d
  , FormatFormulaD d
  , States $qs $q $r
  , Afa.Lib.GetVarsD d
  , Afa.Lib.SplitFinalsMulti2D d
  ) :: Constraint

hPrint :: forall d d1. PrintI d d1 => Handle -> ($r, $r, $qs) -> IO ()
hPrint h (init, final, qs) = do
  initQ <- monadfn @[g1|deref|] init >>= \case
    StateMulti q -> return q
    _unsupported -> error "singleton init expected"

  let initName = identify initQ
  let trueLit = [i|or(l1_#{initName}, -l1_#{initName})|]
  let falseLit = [i|and(l1_#{initName}, -l1_#{initName})|]

  TIO.hPutStrLn h [i|#QCIR-14|]

  vars <- Afa.Lib.getVars @d (init, final, qs)
  (finalnesses, Nothing) <- Afa.Lib.splitFinalsMulti2 @d final qs

  (runConvert, getShared) <- formatFormula @d

  qtrans <- runConvert \convert -> for (stateList qs) \(q, r) -> (q,) <$> convert r
  let qnames = map (identify . fst) qtrans

  let qcount = length qtrans

  case transition finalnesses initQ of
    Afa.Lib.Final -> do
      TIO.hPutStrLn h [i|exists(x)|]
      TIO.hPutStrLn h [i|output(x)|]
    _nonfinal
      | qcount == 1 -> do
          let ls = T.intercalate ", " $ map (\q -> [i|l1_#{q}|]) qnames
          let as = T.intercalate ", " $ map (\a -> [i|a#{identify a}|]) vars
          TIO.hPutStrLn h [i|exists(#{ls})|]
          when (not $ null vars) do
            TIO.hPutStrLn h [i|exists(#{as})|]

          TIO.hPutStrLn h [i|output(ft1)|]

          (rstack, hasTrue, hasFalse) <- getShared
          when hasTrue do TIO.hPutStrLn h [i|fTrue = #{trueLit}|]
          when hasFalse do TIO.hPutStrLn h [i|fFalse = #{falseLit}|]
          for_ (reverse rstack) \(j, txt) -> TIO.hPutStrLn h [i|f#{j} = #{txt}|]

          let fcll = T.intercalate ", " $ stateList finalnesses <&> \case
                (q, Afa.Lib.Final) -> [i|l1_#{identify q}|]
                (q, _nonfinal) -> [i|-l1_#{identify q}|]

          let [(_, r)] = qtrans
          TIO.hPutStrLn h [i|ft1 = and(#{r}, #{fcll})|]

      | otherwise -> do
          let ms = T.intercalate ", " $ map (\q -> [i|m#{qcount}_#{q}|]) qnames
          TIO.hPutStrLn h [i|exists(g#{qcount})|]
          TIO.hPutStrLn h [i|exists(#{ms})|]
          TIO.hPutStrLn h [i|forall(c#{qcount})|]

          for_ [qcount - 1, qcount - 2 .. 2] \step -> do
            let ks = T.intercalate ", " $ map (\q -> [i|k#{step}_#{q}|]) qnames
            let ls = T.intercalate ", " $ map (\q -> [i|l#{step}_#{q}|]) qnames
            let ms = T.intercalate ", " $ map (\q -> [i|m#{step}_#{q}|]) qnames
            TIO.hPutStrLn h [i|exists(h#{step})|]
            TIO.hPutStrLn h [i|exists(g#{step})|]
            TIO.hPutStrLn h [i|exists(#{ks})|]
            TIO.hPutStrLn h [i|exists(#{ls})|]
            TIO.hPutStrLn h [i|exists(#{ms})|]
            TIO.hPutStrLn h [i|forall(c#{step})|]

          let ks = T.intercalate ", " $ map (\q -> [i|k1_#{q}|]) qnames
          let ls = T.intercalate ", " $ map (\q -> [i|l1_#{q}|]) qnames
          let as = T.intercalate ", " $ map (\a -> [i|a#{identify a}|]) vars
          TIO.hPutStrLn h [i|exists(h1)|]
          TIO.hPutStrLn h [i|exists(#{ks})|]
          TIO.hPutStrLn h [i|exists(#{ls})|]
          when (not $ null vars) do
            TIO.hPutStrLn h [i|exists(#{as})|]

          TIO.hPutStrLn h [i|output(ft#{qcount})|]

          (rstack, hasTrue, hasFalse) <- getShared
          when hasTrue do TIO.hPutStrLn h [i|fTrue = #{trueLit}|]
          when hasFalse do TIO.hPutStrLn h [i|fFalse = #{falseLit}|]
          for_ (reverse rstack) \(j, txt) -> TIO.hPutStrLn h [i|f#{j} = #{txt}|]

          for_ qtrans \(q, r) -> do
            TIO.hPutStrLn h [i|fq#{identify q} = or(-k1_#{identify q}, #{r})|]
          let fqs = T.intercalate ", " $ map (\q -> [i|fq#{q}|]) qnames
          TIO.hPutStrLn h [i|fh1 = or(-h1, k1_#{initName})|]
          TIO.hPutStrLn h [i|ft1 = and(fh1, #{fqs})|]

          for_ [2 .. qcount - 1] \step -> do
            TIO.hPutStrLn h [i|fgc#{step} = and(g#{step}, c#{step})|]
            TIO.hPutStrLn h [i|fgct#{step} = or(fgc#{step}, ft#{step - 1})|]
            TIO.hPutStrLn h [i|fhh#{step} = or(-h#{step}, h#{step - 1})|]
            TIO.hPutStrLn h [i|fgh#{step} = or(-g#{step}, h#{step - 1})|]
            for_ qnames \q -> do
              TIO.hPutStrLn h [i|fckk#{step}_#{q} = xor(k#{step - 1}_#{q}, k#{step}_#{q})|]
              TIO.hPutStrLn h [i|fclm#{step}_#{q} = xor(l#{step - 1}_#{q}, m#{step}_#{q})|]
              TIO.hPutStrLn h [i|fckm#{step}_#{q} = xor(k#{step - 1}_#{q}, m#{step}_#{q})|]
              TIO.hPutStrLn h [i|fcll#{step}_#{q} = xor(l#{step - 1}_#{q}, l#{step}_#{q})|]
            let fckk = T.intercalate ", " $ map (\q -> [i|-fckk#{step}_#{q}|]) qnames
            let fclm = T.intercalate ", " $ map (\q -> [i|-fclm#{step}_#{q}|]) qnames
            let fckm = T.intercalate ", " $ map (\q -> [i|-fckm#{step}_#{q}|]) qnames
            let fcll = T.intercalate ", " $ map (\q -> [i|-fcll#{step}_#{q}|]) qnames
            TIO.hPutStrLn h [i|fckklm#{step} = and(fhh#{step}, #{fckk}, #{fclm})|]
            TIO.hPutStrLn h [i|fckmll#{step} = and(fgh#{step}, #{fckm}, #{fcll})|]
            TIO.hPutStrLn h [i|fc#{step} = ite(c#{step}, fckklm#{step}, fckmll#{step})|]
            TIO.hPutStrLn h [i|ft#{step} = and(fc#{step}, fgct#{step})|]

          let step = qcount
          TIO.hPutStrLn h [i|fgc#{step} = and(g#{step}, c#{step})|]
          TIO.hPutStrLn h [i|fgct#{step} = or(fgc#{step}, ft#{step - 1})|]
          TIO.hPutStrLn h [i|fgh#{step} = or(-g#{step}, h#{step - 1})|]
          for_ qnames \q -> do
            TIO.hPutStrLn h [i|fclm#{step}_#{q} = xor(l#{step - 1}_#{q}, m#{step}_#{q})|]
            TIO.hPutStrLn h [i|fckm#{step}_#{q} = xor(k#{step - 1}_#{q}, m#{step}_#{q})|]
          let fclm = T.intercalate ", " $ map (\q -> [i|-fclm#{step}_#{q}|]) qnames
          let fckm = T.intercalate ", " $ map (\q -> [i|-fckm#{step}_#{q}|]) qnames
          let fcll = T.intercalate ", " $ stateList finalnesses <&> \case
                (q, Afa.Lib.Final) -> [i|l#{step - 1}_#{identify q}|]
                (q, _nonfinal) -> [i|-l#{step - 1}_#{identify q}|]
          TIO.hPutStrLn h [i|fckklm#{step} = and(h#{step - 1}, #{fclm})|]
          TIO.hPutStrLn h [i|fckmll#{step} = and(fgh#{step}, #{fckm}, #{fcll})|]
          TIO.hPutStrLn h [i|fc#{step} = ite(c#{step}, fckklm#{step}, fckmll#{step})|]
          TIO.hPutStrLn h [i|ft#{step} = and(fc#{step}, fgct#{step})|]

print :: forall d. PrintD d => ($r, $r, $qs) -> IO ()
print = hPrint @d stdout
