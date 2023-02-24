{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=5 #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Afa.Build
import qualified Afa.Convert.PrettyStranger as PrettyStranger
import qualified Afa.Delit as Delit
import qualified Afa.IORef as AIO
import qualified Afa.Lib as Lib
import qualified Afa.RemoveFinals as RmF
import qualified Afa.Separate as Separ
import Afa.States
import Afa.Term
import Control.Monad.Free
import Data.Fix
import Data.Function.Syntax ((.:))
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Traversable
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import System.Environment
import System.IO

data EmptyO
type instance Definition EmptyO = End

data TextIORefO
type instance
  Definition TextIORefO =
    Name "qs" (PrettyStranger.Qs TextIORef_Ref)
      :+: Name "term" TextIORef_Term
      :+: Follow (Delit.IORefDelitO AIO.IORefO EmptyO)

type TextIORef_Ref = AIO.Ref (Term T.Text T.Text)
type TextIORef_Term = Term T.Text T.Text TextIORef_Ref

prettyToPretty :: IO ()
prettyToPretty = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  PrettyStranger.print @TextIORefO afa

removeSingleInit :: IO ()
removeSingleInit = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.removeSingleInit @TextIORefO afa
  PrettyStranger.print @TextIORefO afa'

addInit :: IO ()
addInit = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.addInit @TextIORefO afa
  PrettyStranger.print @(Lib.AddInitO TextIORefO) afa'

complement :: IO ()
complement = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Just afa' <- Lib.complement @TextIORefO afa
  PrettyStranger.print @TextIORefO afa'

unshare :: IO ()
unshare = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.unshare @TextIORefO afa
  PrettyStranger.print @TextIORefO afa'

initToDnf :: IO ()
initToDnf = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  init' <- Lib.singleToDnf @TextIORefO init
  PrettyStranger.print @TextIORefO (init', final, qs)

boomSeparate :: IO ()
boomSeparate = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  qs1 <- Separ.boomSeparate @TextIORefO qs
  qs2 <- Separ.unseparate @TextIORefO qs1
  PrettyStranger.print @TextIORefO (init, final, qs2)

isSeparated :: IO ()
isSeparated = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Separ.trySeparate @TextIORefO qs >>= \case
    Just _ -> return ()
    Nothing -> error "not separated"

qdnf :: IO ()
qdnf = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Just qs1 <- Separ.trySeparate @TextIORefO qs
  qs2 <- Lib.qdnf @(Separ.SeparateO TextIORefO) qs1
  qs3 <- Separ.unseparate @TextIORefO qs2
  PrettyStranger.print @TextIORefO (init, final, qs3)

qombo ::
  forall d.
  (d ~ Lib.QomboO TextIORefO) =>
  [String] ->
  ([Free (Term $q $v) $r] -> Free (Term $q $v) $r) ->
  IO ()
qombo paths fn = do
  afas <- for paths \path -> do
    f <- openFile path ReadMode
    txt <- TIO.hGetContents f
    PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.qombo @TextIORefO fn afas
  PrettyStranger.print @d afa'

removeFinals ::
  forall d build.
  ( d ~ RmF.RemoveFinalsO TextIORefO
  , build ~ Inherit (Explicit [g|term|] $r) [k|build|]
  ) =>
  IO ()
removeFinals = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  (init1, qs1) <- RmF.removeFinals @TextIORefO afa
  final1 <-
    buildFix @build $
      foldr (Fix .: And . Fix . Not . Fix . State . fst) (Fix LTrue) (stateList qs1)
  PrettyStranger.print @d (init1, final1, qs1)

removeFinalsHind ::
  forall d build.
  ( d ~ RmF.RemoveFinalsHindO TextIORefO
  , build ~ Inherit (Explicit [g|term|] $r) [k|build|]
  ) =>
  IO ()
removeFinalsHind = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Just qs1 <- Separ.trySeparate @TextIORefO qs
  (init2, qs2) <- RmF.removeFinalsHind @(Separ.SeparateO TextIORefO) (init, final, qs1)
  final2 <-
    buildFix @build $
      foldr (Fix .: And . Fix . Not . Fix . State . fst) (Fix LTrue) (stateList qs2)
  qs3 <- Separ.unseparate @d qs2
  PrettyStranger.print @d (init2, final2, qs3)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["prettyToPretty"] -> prettyToPretty
    ["removeSingleInit"] -> removeSingleInit
    ["addInit"] -> addInit
    ["complement"] -> complement
    ["unshare"] -> unshare
    ["initToDnf"] -> initToDnf
    ["boomSeparate"] -> boomSeparate
    ["isSeparated"] -> isSeparated
    ["qdnf"] -> qdnf
    ("and" : paths) -> qombo paths (foldr1 $ Free .: And)
    ("or" : paths) -> qombo paths (foldr1 $ Free .: Or)
    ("neq" : paths) -> qombo paths \[a, b, na, nb] ->
      Free $ Or (Free $ And a nb) (Free $ And na b)
    ["removeFinals"] -> removeFinals
    ["removeFinalsHind"] -> removeFinalsHind
