{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
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
import Data.Foldable
import Data.Function.Syntax ((.:))
import Data.Functor
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Traversable
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import System.Environment
import System.Exit
import System.IO
import Data.IORef
import Data.String.Interpolate.IsString (i)

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
    Just _ -> exitSuccess
    Nothing -> exitFailure

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

hasComplexFinals :: IO ()
hasComplexFinals = do
  txt <- TIO.getContents
  (_, final, _) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Lib.splitFinals @TextIORefO final >>= \case
    (_, Just _) -> exitSuccess
    _ -> exitFailure

delaySymbolsLowest :: IO ()
delaySymbolsLowest = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.delay @TextIORefO @Zero afa \r ->
    AIO.deref r <&> \case
      Var _ -> True
      Not _ -> True
      LFalse -> True
      _ -> False
  PrettyStranger.print @(Lib.DelayO TextIORefO) afa'

share :: IO ()
share = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  shareR <- AIO.getSharingDetector
  afa' <- (,,) <$> shareR init <*> shareR final <*> traverseR shareR qs
  PrettyStranger.print @TextIORefO afa'

removeUselessShares :: IO ()
removeUselessShares = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  (countUpR, finalize) <- AIO.getUnsharingDetector \case
    Not _ -> True
    And _ _ -> True
    Or _ _ -> True
    _ -> False
  countUpR init <> countUpR final <> void (traverseR countUpR qs)
  finalizeR <- finalize
  afa' <- (,,) <$> finalizeR init <*> finalizeR final <*> traverseR finalizeR qs
  PrettyStranger.print @TextIORefO afa'

checkerV1RemoveFinalsNonsep :: IO ()
checkerV1RemoveFinalsNonsep = do
  txt <- TIO.getContents
  (init, final, StateHashMap qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  case HM.lookup "Sync" qs of
    Nothing -> exitSuccess
    Just qITrans -> do
      let replaceI :: AIO.Ref (Term T.Text T.Text) -> IO (AIO.Ref (Term T.Text T.Text))
          replaceI r = do
            AIO.deref r >>= \case
              And a b -> do
                a' <- AIO.deref a
                b' <- AIO.deref b
                let build = if AIO.isTree r then return . AIO.Subtree else AIO.shareTree
                case (a', b') of
                  (State "Sync", _) -> build (And qITrans b)
                  (_, State "Sync") -> build (And a qITrans)
                  _ -> build =<< And <$> replaceI a <*> replaceI b
              _ -> return r

      init1 <- AIO.share init
      init2 <- AIO.share =<< replaceI init

      let findAsQs ::
            AIO.Ref (Term T.Text T.Text) ->
            IO (Endo [T.Text], Endo [T.Text])
          findAsQs r = do
            AIO.deref r >>= \case
              State q -> return (mempty, Endo (q :))
              Var v -> return (Endo (v :), mempty)
              fr -> fold <$> mapM findAsQs fr
      ((`appEndo` []) -> as, (`appEndo` []) -> qs) <- findAsQs init2

      let toText :: AIO.Ref (Term T.Text T.Text) -> IO T.Text
          toText r = do
            AIO.deref r >>= \case
              LTrue -> return "TRUE"
              LFalse -> return "FALSE"
              State q -> return [i|q#{q}|]
              Var v -> return [i|a#{v}|]
              And a b -> do
                a' <- toText a
                b' <- toText b
                return [i|(#{a'} & #{b'})|]
              Or a b -> do
                a' <- toText a
                b' <- toText b
                return [i|(#{a'} | #{b'})|]
              Not a -> do
                a' <- toText a
                return [i|!#{a'}|]

      init1T <- toText init1
      init2T <- toText init2
      let cond :: T.Text
          cond = [i|SPEC AG(#{init1T} = #{init2T})|]

      TIO.putStrLn "MODULE main"
      TIO.putStrLn "VAR"
      for_ (HS.fromList as) \a ->
        TIO.putStrLn [i|  a#{a}: boolean;|]
      for_ (HS.fromList qs) \q ->
        TIO.putStrLn [i|  q#{q}: boolean;|]
      TIO.putStrLn "  dummy: boolean;"
      TIO.putStrLn "ASSIGN"
      TIO.putStrLn "  init(dummy) := TRUE;"
      TIO.putStrLn "  next(dummy) := TRUE;"
      TIO.putStrLn cond
      exitFailure

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
    ["hasComplexFinals"] -> hasComplexFinals
    ["delaySymbolsLowest"] -> delaySymbolsLowest
    ["share"] -> share
    ["removeUselessShares"] -> removeUselessShares
    ["checkerV1RemoveFinalsNonsep"] -> checkerV1RemoveFinalsNonsep
