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
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=5 #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Afa.Build
import qualified Afa.Convert.PrettyStranger as PrettyStranger
import qualified Afa.Convert.Vtf as Vtf
import qualified Afa.Convert.Ltl as Ltl
import qualified Afa.Convert.Smv as Smv
import qualified Afa.Convert.Qcir as Qcir
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
import Data.Maybe
import Data.Monoid
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Traversable
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict
import System.Environment
import System.Exit
import System.IO

data EmptyO
type instance Definition EmptyO = End

data TextIORefO
type instance Definition TextIORefO =
  Name "qs" (PrettyStranger.Qs TextIORef_Ref)
    :+: Name "term" TextIORef_Term
    -- :+: Follow (AIO.IORefO EmptyO)
    :+: Follow (Delit.DelitO AIO.IORefO EmptyO)

type TextIORef_Ref = AIO.Ref (Term T.Text T.Text)
type TextIORef_Term = Term T.Text T.Text TextIORef_Ref

flattenAndHPrint ::
  forall d.
  (Lib.FlattenD d, PrettyStranger.PrintD (Lib.FlattenO d)) =>
  Handle -> ($r, $r, $qs) -> IO ()
flattenAndHPrint h afa = do
  afa' <- Lib.flatten @d afa
  PrettyStranger.hPrint @(Lib.FlattenO d) h afa'

flattenAndPrint ::
  forall d.
  (Lib.FlattenD d, PrettyStranger.PrintD (Lib.FlattenO d)) =>
  ($r, $r, $qs) -> IO ()
flattenAndPrint = flattenAndHPrint @d stdout

prettyToPretty :: IO ()
prettyToPretty = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  flattenAndPrint @TextIORefO afa

prettyToSmv :: IO ()
prettyToSmv = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.flatten @TextIORefO afa
  Smv.hPrint @(Lib.FlattenO TextIORefO) stdout afa'

prettyToQcir :: IO ()
prettyToQcir = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.flatten @TextIORefO afa
  Qcir.hPrint @(Lib.FlattenO TextIORefO) stdout afa'

removeSingleInit :: IO ()
removeSingleInit = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.removeSingleInit @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

addInit :: IO ()
addInit = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.addInit @TextIORefO afa
  flattenAndPrint @(Lib.AddInitO TextIORefO) afa'

complement :: IO ()
complement = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Just afa' <- Lib.complement @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

unshare :: IO ()
unshare = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.unshare @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

initToDnf :: IO ()
initToDnf = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  init' <- Lib.singleToDnf @TextIORefO init
  flattenAndPrint @TextIORefO (init', final, qs)

boomSeparate :: IO ()
boomSeparate = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  qs1 <- Separ.boomSeparate @TextIORefO qs
  qs2 <- Separ.unseparate @(Separ.SeparateO TextIORefO) qs1
  flattenAndPrint @TextIORefO (init, final, qs2)

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
  qs3 <- Separ.unseparate @(Separ.SeparateO TextIORefO) qs2
  flattenAndPrint @TextIORefO (init, final, qs3)

qombo ::
  forall d.
  (d ~ Lib.QomboO TextIORefO) =>
  [String] ->
  ([Free (Term $q $v) $r] -> Free (Term $q $v) $r) ->
  IO ()
qombo paths fn = do
  afas <- for paths \path -> do
    withFile path ReadMode \f -> do
      txt <- TIO.hGetContents f
      PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.qombo @TextIORefO fn afas
  flattenAndPrint @d afa'

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
  flattenAndPrint @d (init1, final1, qs1)

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
  flattenAndPrint @(Separ.UnseparateO d) (init2, final2, qs3)

hasComplexFinals :: IO ()
hasComplexFinals = do
  txt <- TIO.getContents
  (_, final, _) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Lib.splitFinals @TextIORefO final >>= \case
    (_, Just _) -> exitSuccess
    _ -> exitFailure

hasFinals :: IO ()
hasFinals = do
  txt <- TIO.getContents
  (_, final, _) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  Lib.splitFinals @TextIORefO final >>= \case
    ([], Nothing) -> exitFailure
    _ -> exitSuccess

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
  flattenAndPrint @(Lib.DelayO TextIORefO) afa'

flatShare :: IO ()
flatShare = do
  txt <- TIO.getContents
  afa' <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  (init, final, qs) <- Lib.flatten @TextIORefO afa'
  shareR <- AIO.getSharingDetector sameTraverse
  afa' <- (,,) <$> shareR init <*> shareR final <*> traverseR shareR qs
  PrettyStranger.print @(Lib.FlattenO TextIORefO) afa'

share :: IO ()
share = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  shareR <- AIO.getSharingDetector traverse
  afa' <- (,,) <$> shareR init <*> shareR final <*> traverseR shareR qs
  flattenAndPrint @TextIORefO afa'

removeUselessShares :: IO ()
removeUselessShares = do
  txt <- TIO.getContents
  (init, final, qs) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  (countUpR, finalize) <- AIO.getUnsharingDetector \case
    Not _ -> True
    And _ _ -> True
    Or _ _ -> True
    _terminal -> False
  countUpR init <> countUpR final <> void (traverseR countUpR qs)
  finalizeR <- finalize
  afa' <- (,,) <$> finalizeR init <*> finalizeR final <*> traverseR finalizeR qs
  flattenAndPrint @TextIORefO afa'

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

vtfToPretty :: IO ()
vtfToPretty = do
  txt <- TIO.getContents
  (init, final, qs) <- Vtf.parse @TextIORefO $ Vtf.parseStatements txt
  qs' <- Separ.unseparate @(Separ.SeparateO TextIORefO) qs
  flattenAndPrint @TextIORefO (init, final, qs')

explicitToBitvector :: [String] -> IO ()
explicitToBitvector paths = do
  afas <- for paths \path -> do
    withFile path ReadMode \f -> do
      txt <- TIO.hGetContents f
      PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)

  afas' <- Lib.explicitToBitvector @TextIORefO afas

  for_ (zip afas' paths) \(afa, path) -> do
    let barePath = fromJust $ T.stripSuffix ".afa" $ T.pack path
    let path' = T.unpack (T.append barePath ".bitvector.afa")
    withFile path' WriteMode \f ->
      flattenAndHPrint @(Lib.ExplicitToBitvectorO TextIORefO) f afa

removeUnreachable :: IO ()
removeUnreachable = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.removeUnreachable @TextIORefO afa
  flattenAndPrint @(Lib.RemoveUnreachableO TextIORefO) afa'

removeUnisignVariables :: IO ()
removeUnisignVariables = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.removeUnisignVariables @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

removeLitStates :: IO ()
removeLitStates = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.removeLitStates @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

pushPosNot :: IO ()
pushPosNot = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.pushPosNot @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

tseytin :: IO ()
tseytin = do
  txt <- TIO.getContents
  !afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  cnfAfa@Lib.CnfAfa{..} <- Lib.tseytin @TextIORefO afa
  print variableCount
  putStrLn $ unwords [show if pos then x + 1 else -x - 1 | (pos, x) <- outputs]
  putStrLn $ unwords $ map show finals
  putStrLn $ unwords $ map show pureVars
  putStrLn $ unwords $ map show upwardClauses
  putStrLn $ unwords $ map show posqOutputs
  for_ clauses \(optional, clause) -> do
    putStr $ unwords [show if pos then x + 1 else -x - 1 | (pos, x) <- clause]
    putStrLn $ if optional then " 0" else ""

shareStates :: IO ()
shareStates = do
  txt <- TIO.getContents
  afa <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  afa' <- Lib.shareStates @TextIORefO afa
  flattenAndPrint @TextIORefO afa'

ltlToPretty :: IO ()
ltlToPretty = do
  txt <- TIO.getContents
  afa <- Ltl.textToAfa txt
  PrettyStranger.print @Ltl.AfaO afa

hasSimpleInit :: IO ()
hasSimpleInit = do
  txt <- TIO.getContents
  (init, _, _) <- PrettyStranger.parse @TextIORefO (PrettyStranger.parseDefinitions txt)
  AIO.deref init >>= \case
    State _ -> exitSuccess
    _nonSimple -> exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["prettyToPretty"] -> prettyToPretty
    ["prettyToSmv"] -> prettyToSmv
    ["prettyToQcir"] -> prettyToQcir
    ["removeSingleInit"] -> removeSingleInit
    ["addInit"] -> addInit
    ["hasSimpleInit"] -> hasSimpleInit
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
    ["hasFinals"] -> hasFinals
    ["hasComplexFinals"] -> hasComplexFinals
    ["delaySymbolsLowest"] -> delaySymbolsLowest
    ["flatShare"] -> flatShare
    ["share"] -> share
    ["removeUselessShares"] -> removeUselessShares
    ["checkerV1RemoveFinalsNonsep"] -> checkerV1RemoveFinalsNonsep
    ["vtfToPretty"] -> vtfToPretty
    ("explicitToBitvector" : paths) -> explicitToBitvector paths
    ["removeUnreachable"] -> removeUnreachable
    ["removeUnisignVariables"] -> removeUnisignVariables
    ["removeLitStates"] -> removeLitStates
    ["pushPosNot"] -> pushPosNot
    ["tseytin"] -> tseytin
    ["shareStates"] -> shareStates
    ["ltlToPretty"] -> ltlToPretty
    _unsupportedArguments -> do
      hPutStrLn stderr $ "Unsupported arguments " ++ show args
      exitFailure
