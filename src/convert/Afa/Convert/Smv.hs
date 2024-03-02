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

module Afa.Convert.Smv where

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
    , IO [(Int, T.Text)]
    )
formatFormula = do
  vFIx <- newIORef (0 :: Int)
  stack <- newIORef ([] :: [(Int, T.Text)])

  let algebra :: ($r -> t IO T.Text) -> ($r, [g|term|]) -> t IO T.Text
      algebra rec (r, fr) = do
        lift (monadfn @[g1|isTree|] r) >>= \case
          True -> contents
          False -> do
            txt <- contents
            fIx <- lift $ readIORef vFIx
            lift $ writeIORef vFIx $ fIx + 1
            lift $ modifyIORef stack ((fIx, txt) :)
            return $ do T.cons 'f' (T.pack (show fIx))
        where
          contents :: R.Et [g1|rec|] IO T.Text
          contents =
            case fr of
              LTrueMulti -> return "TRUE"
              LFalseMulti -> return "FALSE"
              StateMulti q -> return $ T.cons 'q' (identify q)
              VarMulti v -> return $ T.cons 'a' (identify v)
              NotMulti !r -> do
                T.cons '!' <$> rec r
              AndMulti (map unshallow . HS.toList -> xs) -> do
                !xs' <- mapM rec xs
                return $ T.concat ["(", T.intercalate " & " xs', ")"]
              OrMulti (map unshallow . HS.toList -> xs) -> do
                !xs' <- mapM rec xs
                return $ T.concat ["(", T.intercalate " | " xs', ")"]

  return (R.runRecur @[g1|rec|] algebra, readIORef stack)

unparen :: T.Text -> T.Text
unparen t = case T.uncons t of
  Just ('(', t') -> T.init t'
  _ -> t


type PrintD d =
  ( FormatFormulaD d
  , States $qs $q $r
  , Afa.Lib.GetVarsD d
  , Afa.Lib.SplitFinalsMulti2D d
  ) :: Constraint

hPrint :: forall d. PrintD d => Handle -> ($r, $r, $qs) -> IO ()
hPrint h (init, final, qs) = do
  (runConvert, getShared) <- formatFormula @d

  vars <- Afa.Lib.getVars @d (init, final, qs)
  (finalnesses, complexFinals) <- Afa.Lib.splitFinalsMulti2 @d final qs

  (init', complexFinals', qtrans) <- runConvert \convert -> (,,)
    <$> convert init
    <*> for complexFinals convert
    <*> for (stateList qs) \(q, r) -> (q,) <$> convert r

  TIO.hPutStrLn h "MODULE main"

  TIO.hPutStrLn h "VAR"
  for_ qtrans \(q, _) -> TIO.hPutStrLn h [i|  q#{identify q}: boolean;|]
  for_ vars \v -> TIO.hPutStrLn h [i|  a#{identify v}: boolean;|]

  TIO.hPutStrLn h "DEFINE"
  getShared >>= mapM_ \(j, txt) -> TIO.hPutStrLn h [i|  f#{j} := #{unparen txt};|]

  TIO.hPutStrLn h "ASSIGN"
  for_ qtrans \(q, tran) -> do
    case transition finalnesses q of
      Afa.Lib.Final -> do TIO.hPutStrLn h [i|  init(q#{identify q}) := TRUE;|]
      Afa.Lib.Nonfinal -> TIO.hPutStrLn h [i|  init(q#{identify q}) := FALSE;|]
      Afa.Lib.Complex -> return ()
    TIO.hPutStrLn h [i|  next(q#{identify q}) := #{unparen tran};|]

  for_ complexFinals' \f -> TIO.hPutStrLn h [i|INIT #{unparen f}|]
  TIO.hPutStrLn h [i|SPEC AG(!(#{unparen init'}))|]

print :: forall d. PrintD d => ($r, $r, $qs) -> IO ()
print = hPrint @d stdout
