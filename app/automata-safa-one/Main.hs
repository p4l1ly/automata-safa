{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import qualified Afa.Convert.PrettyStranger as PrettyStranger
import qualified Afa.IORef as AIO
import qualified Afa.Delit as Delit
import Afa.Term
import qualified Afa.Lib as Lib
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import System.Environment

data EmptyD
type instance Definition EmptyD = End

data TextIORefD
type instance
  Definition TextIORefD =
    Name "term" (Term T.Text T.Text (AIO.Ref (Term T.Text T.Text)))
      :+: Follow (Delit.IORefDelitO AIO.IORefO EmptyD Zero)

prettyToPretty :: IO ()
prettyToPretty = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefD (PrettyStranger.parseDefinitions txt)
  PrettyStranger.format @TextIORefD afa

unInitState :: IO ()
unInitState = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefD (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.unInitState @TextIORefD afa
  PrettyStranger.format @TextIORefD afa'

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["prettyToPretty"] -> prettyToPretty
    ["unInitState"] -> unInitState
