{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Afa hiding (simplifyAll)
import qualified Afa
import Afa.Bool
import Afa.Convert.Ada (toAda)
import qualified Afa.Convert.Ada2 as Ada2
import qualified Afa.Convert.AdaBits as AdaBits
import Afa.Convert.Capnp.Afa
import Afa.Convert.Capnp.CnfAfa (hWriteCnfAfa)
import qualified Afa.Convert.Capnp.Range16Nfa as Range16Nfa
import qualified Afa.Convert.Capnp.Separated as SepCap
import Afa.Convert.CnfAfa (tseytin')
import Afa.Convert.Dot
import Afa.Convert.Ltle
import qualified Afa.Convert.Machete as Machete
import qualified Afa.Convert.Mona as Mona
import qualified Afa.Convert.PrettyStranger as PrettyStranger
import qualified Afa.Convert.PrettyStranger2 as PrettyStranger2
import qualified Afa.Convert.Separated as Sep
import qualified Afa.Convert.Separated.Model as Sep
import qualified Afa.Convert.Separated.ToDnf as ToDnf
import qualified Afa.Convert.Separated2 as Sep2
import Afa.Convert.Smv
import qualified Afa.Convert.Smv2 as Smv2
import qualified Afa.Convert.Stranger as Stranger
import qualified Afa.Convert.Stranger2 as Stranger2
import qualified Afa.Finalful as Finalful
import qualified Afa.Finalful.STerm
import qualified Afa.Finalful.STerm as STerm
import qualified Afa.IORef
import qualified Afa.Negate as Negate
import qualified Afa.Ops.Boolean as Ops
import Afa.Ops.Compound
import Afa.Ops.Randomize (randomizeIO)
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Control.Monad.Free
import Data.Array
import Data.Fix (Fix (..))
import Data.Foldable (toList)
import Data.Function.Apply ((-$))
import Data.Function.Syntax ((.:))
import Data.Functor
import Data.Functor.Base
import Data.Functor.Compose
import Data.Functor.Foldable
import Data.Functor.Identity
import qualified Data.HashMap.Strict as HM
import Data.List
import Data.List.Split
import Data.Maybe
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Time.Clock.POSIX (getPOSIXTime)
import Data.Traversable
import Data.Void (Void)
import Data.Word (Word32, Word8)
import Debug.Trace
import Ltl.Parser
import Options.Applicative
import qualified Shaper
import qualified Shaper.Helpers
import System.Directory
import System.Environment (getArgs)
import System.IO
import Text.Read
import TypeDict (TypeDict ((:+:)), d)
import qualified TypeDict

data Opts = Opts
  { readers :: Fix (Compose IO (ListF (String, BoolAfaUnswallowed Int)))
  , writers :: [String -> BoolAfaUnswallowed Int -> Either Bool ((Int, Int, Int), IO ())]
  }

dirReaders :: forall a. Int -> (Handle -> IO a) -> String -> Fix (Compose IO (ListF (String, a)))
dirReaders count fileReader indir = Fix $
  Compose $ do
    (sort . map read -> files0 :: [Int]) <- listDirectory indir
    reader (project $ zip [0 ..] files0) <&> \case
      Nil -> Nil
      Cons afa a -> Cons afa $ hoist (Compose . reader) (a :: [(Int, Int)])
  where
    reader :: ListF (Int, Int) b -> IO (ListF (String, a) b)
    reader Nil = return Nil
    reader (Cons (i, _) _) | i == count = return Nil
    reader (Cons (_, file) a) = do
      afa <- withFile (indir ++ "/" ++ show file) ReadMode fileReader
      return $ Cons (show file, afa) a

strangerReaders ::
  (T.Text -> BoolAfaUnswallowed Int) ->
  String ->
  Fix (Compose IO (ListF (String, BoolAfaUnswallowed Int)))
strangerReaders parseAfa = dirReaders maxBound $ \h -> TIO.hGetContents h <&> parseAfa

arrSize :: Array Int a -> Int
arrSize = rangeSize . bounds

mtermNCount :: Array Int (MTerm.Term p q t) -> Int
mtermNCount arr = length $
  ($ elems arr) $
    filter $
      \case MTerm.And _ -> True; MTerm.Or _ -> True; _ -> False

btermNCount :: Array Int (BTerm.Term p t) -> Int
btermNCount arr = length $
  ($ elems arr) $
    filter $
      \case BTerm.And _ -> True; BTerm.Or _ -> True; _ -> False

edgeCount :: (Functor f, Foldable f, Foldable g) => f (g a) -> Int
edgeCount = sum . fmap length

afaCosts bafa = (qCount, nCount, eCount)
  where
    qafa = afa bafa
    qCount = arrSize $ states qafa
    nCount = btermNCount (boolTerms bafa) + mtermNCount (terms qafa)
    eCount = edgeCount (terms qafa) + edgeCount (boolTerms bafa)

sepAfaCosts sepafa = (qCount, nCount, eCount)
  where
    qCount = arrSize $ Sep.states sepafa
    nCount =
      btermNCount (Sep.aterms sepafa) + mtermNCount (Sep.qterms sepafa)
        + sum (Sep.states sepafa <&> length . filter (\(a, q) -> isJust a && isJust q))
    eCount =
      edgeCount (Sep.aterms sepafa) + edgeCount (Sep.qterms sepafa)
        + sum (Sep.states sepafa <&> length)
        + sum (Sep.states sepafa <&> (2 *) . length . filter (\(a, q) -> isJust a && isJust q))

afaWriter outdir i (reorderStates' -> bafa) =
  ( afaCosts bafa
  , withFile (outdir ++ "/" ++ i) WriteMode $ hWriteAfa True bafa
  )

afaWriter0 outdir i (reorderStates' -> bafa) =
  ( afaCosts bafa
  , withFile (outdir ++ "/" ++ i) WriteMode $ hWriteAfa False bafa
  )

sepAfaWriter outdir i (Sep.reorderStates' -> sepafa) =
  ( sepAfaCosts sepafa
  , withFile (outdir ++ "/" ++ i) WriteMode $ SepCap.hWrite sepafa
  )

parseIxList :: String -> [Int]
parseIxList = map read . splitOn ","

equality afa1 afa2 =
  Ops.union
    (Ops.intersection afa1 (Ops.complementUnsafeShallow afa2))
    (Ops.intersection afa2 (Ops.complementUnsafeShallow afa1))

inclusion afa1 afa2 = Ops.intersection afa1 (Ops.complementUnsafeShallow afa2)

optParser :: Parser Opts
optParser =
  Opts
    <$> option
      ( eitherReader $ \case
          "ltl" -> Right $
            flip ana 0 $ \i ->
              Compose $
                ( getLine <&> parseLtl <&> ltleToUnswallowedAfa
                    <&> (show i,)
                    <&> flip Cons (i + 1)
                )
                  `catch` \(SomeException _) -> return Nil
          (splitOn ":" -> ["afai", read -> i, indir]) -> Right $ dirReaders i hReadAfa indir
          (break (== ':') -> ("afa", ':' : indir)) -> Right $ dirReaders maxBound hReadAfa indir
          (break (== ':') -> ("sepafa", ':' : indir)) ->
            Right $ dirReaders maxBound (fmap Sep.separatedToMixed . SepCap.hRead) indir
          (break (== ':') -> ("stranger", ':' : indir)) -> Right $ strangerReaders Stranger.parseAfa indir
          (break (== ':') -> ("prettyStranger", ':' : indir)) -> Right $ strangerReaders PrettyStranger.parseAfa indir
          (break (== ':') -> ("range16nfa", ':' : indir)) ->
            Right $
              dirReaders maxBound Range16Nfa.hReadNfa indir
          ( splitOn ":" ->
              [ "conjunctEq"
                , parseIxList -> conjunct1
                , parseIxList -> conjunct2
                , indir
                ]
            ) -> Right $
              flip ana 0 $ \i ->
                Compose $
                  do
                    files <- words <$> getLine
                    [afa1, afa2] <- for [conjunct1, conjunct2] $ \ixs -> do
                      afas <- for (map (files !!) ixs) $ \file ->
                        withFile (indir ++ "/" ++ file) ReadMode hReadAfa
                      return $ foldr1 Ops.intersection afas
                    return $ Cons (show i, equality afa1 afa2) (i + 1)
                    `catch` \(SomeException exc) -> do
                      hPrint stderr exc
                      return Nil
          ( splitOn ":" ->
              [ "inclusion"
                , indir1
                , indir2
                ]
            ) -> Right $
              flip ana 1 $ \i ->
                Compose $
                  do
                    [afa1, afa2] <- for [indir1, indir2] $ \indir ->
                      withFile (indir ++ "/" ++ show i) ReadMode hReadAfa
                    return $ Cons (show i, inclusion afa1 afa2) (i + 1)
                    `catch` \(SomeException exc) -> do
                      hPrint stderr exc
                      return Nil
          ( splitOn ":" ->
              [ "intersection"
                , indir1
                , indir2
                ]
            ) -> Right $
              flip ana 1 $ \i ->
                Compose $
                  do
                    [afa1, afa2] <- for [indir1, indir2] $ \indir ->
                      withFile (indir ++ "/" ++ show i) ReadMode hReadAfa
                    return $ Cons (show i, Ops.intersection afa1 afa2) (i + 1)
                    `catch` \(SomeException exc) -> do
                      hPrint stderr exc
                      return Nil
          x -> Left $ "expected one of: ltl, afa:<path>; got " ++ x
      )
      ( long "input"
          <> short 'i'
          <> help "Input format: ltl, afa:<path>"
      )
    <*> option
      ( eitherReader $ \case
          "isValid" ->
            Right $ repeat $ \i bafa -> Right ((0, 0, 0), hPrint stderr $ isValid bafa)
          (break (== ':') -> ("afa", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ afaWriter outdir i bafa
          (break (== ':') -> ("afa0", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ afaWriter0 outdir i (unswallow $ swallow bafa)
          (break (== ':') -> ("swallowUnswallow", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ afaWriter0 outdir i bafa
          (break (== ':') -> ("cnfafa0", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $
                  (afaCosts bafa,) $
                    withFile (outdir ++ "/" ++ i) WriteMode $
                      hWriteCnfAfa $
                        tseytin' $ hashConsBoolAfa $ replaceLits bafa
          (break (== ':') -> ("afaHashCons", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ afaWriter0 outdir i $ hashConsBoolAfa bafa
          (break (== ':') -> ("afaRandomized", ':' : outdir)) ->
            Right $
              repeat $ \i bafa -> Right $
                (afaCosts bafa,) $ do
                  bafa' <- randomizeIO bafa
                  withFile (outdir ++ "/" ++ i) WriteMode $ hWriteAfa True (reorderStates' bafa')
          (break (== ':') -> ("afaBasicSimp", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                simplifyAll bafa <&> afaWriter outdir i
          (break (== ':') -> ("afaBasicSimp0", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                simplifyAll bafa <&> afaWriter0 outdir i
          (break (== ':') -> ("afaSimpGoblinMincut", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                simpGoblinMincutUntilFixpoint bafa <&> afaWriter outdir i
          (break (== ':') -> ("afaSimpGoblinMincut1", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                simpGoblinMincut bafa <&> afaWriter outdir i
          (break (== ':') -> ("afaSimpGoblin", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                simpGoblin bafa <&> afaWriter outdir i
          (break (== ':') -> ("afaSimpMincut", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                simpMincut bafa <&> afaWriter outdir i
          (break (== ':') -> ("cnfafa", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $
                  (afaCosts bafa,) $
                    withFile (outdir ++ "/" ++ i) WriteMode $ hWriteCnfAfa $ tseytin' bafa
          (break (== ':') -> ("sepafaExploding", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                let Just sepafa =
                      Sep.mixedToSeparated bafa
                        <|> Sep.mixedToSeparated bafa{afa = Sep.separabilizeAfa $ afa bafa}
                 in Sep.simplify sepafa <&> sepAfaWriter outdir i
          (break (== ':') -> ("sepafaDelaying", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                let Just sepafa =
                      Sep.mixedToSeparated bafa
                        <|> Sep.mixedToSeparated bafa{afa = delayPredicates $ afa bafa}
                 in Sep.simplify sepafa <&> sepAfaWriter outdir i
          (break (== ':') -> ("dnfsepafaDelaying", ':' : outdir)) ->
            Right $
              repeat $ \i (separateStatelessBottoms -> bafa) -> do
                let Just sepafa =
                      Sep.mixedToSeparated bafa
                        <|> Sep.mixedToSeparated bafa{afa = delayPredicates $ afa bafa}
                sepafa' <- Sep.simplify sepafa
                let sepafa''
                      | all (\case MTerm.Or _ -> False; _ -> True) $ Sep.qterms sepafa = traceShow (i, "dnfOk") sepafa
                      | otherwise = case ToDnf.distributeTopOrs sepafa' of
                        Just sepafa'' -> traceShow (i, "distributeTopOrs") sepafa''
                        Nothing -> traceShow (i, "epsilonize") $ ToDnf.epsilonize sepafa'
                Sep.simplify sepafa'' <&> sepAfaWriter outdir i
          (break (== ':') -> ("smv", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ (afaCosts bafa,) $ TIO.writeFile (outdir ++ "/" ++ i) $ toSmv bafa
          (break (== ':') -> ("smvReverse", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ (afaCosts bafa,) $ TIO.writeFile (outdir ++ "/" ++ i) $ toSmvReverse bafa
          (break (== ':') -> ("smvReverseAssign", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ (afaCosts bafa,) $ TIO.writeFile (outdir ++ "/" ++ i) $ toSmvReverseAssign bafa
          (break (== ':') -> ("dot", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $
                  (afaCosts bafa,) $
                    TIO.writeFile (outdir ++ "/" ++ i) $
                      toDot True $
                        let bafa' = separateStatelessBottoms bafa
                         in bafa'{afa = (\(Right x) -> x) $ Afa.simplifyAll $ afa bafa'}
          (break (== ':') -> ("ada", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ (afaCosts bafa,) $ TIO.writeFile (outdir ++ "/" ++ i) $ toAda bafa
          (break (== ':') -> ("stranger", ':' : outdir)) ->
            Right $
              repeat $ \i bafa ->
                Right $ (afaCosts bafa,) $ TIO.writeFile (outdir ++ "/" ++ i) $ Stranger.formatAfa bafa
          (break (== ':') -> ("prettyStranger", ':' : outdir)) ->
            Right $
              repeat $ \i (separateStatelessBottoms -> bafa) ->
                Right $ (afaCosts bafa,) $ TIO.writeFile (outdir ++ "/" ++ i) $ PrettyStranger.formatAfa bafa
          x ->
            Left $
              "expected one of: \
              \{afa,afaBasicSimp,cnfafa,sepafaExploding,sepafaDelaying}:<path>; got "
                ++ x
      )
      ( long "output"
          <> short 'o'
          <> help
            "Output format: \
            \{afa,afaBasicSimp,cnfafa,sepafaExploding,sepafaDelaying}:<path>"
      )

timeoutMicro = 500 * 1000000

removeFinalsMain ::
  forall d t r buildTree buildD q' v' r'.
  ( t ~ T.Text
  , q' ~ Finalful.SyncQs t
  , v' ~ Finalful.SyncVar t t
  , r' ~ Afa.IORef.Ref (STerm.Term q' v')
  , d ~ Afa.IORef.IORefRemoveFinalsD t t r r
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term q' v' r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
removeFinalsMain = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init2, final2, qs) <- PrettyStranger2.parseIORef $ Stranger2.parseDefinitions $ T.pack txt
  hPutStrLn stderr "separating"
  Just qs1 <- Afa.IORef.trySeparateQTransitions qs
  hPutStrLn stderr "removing finals"
  (init3, qs2) <- Afa.IORef.removeFinalsHind init2 final2 qs1
  hPutStrLn stderr "unseparating"
  qs3@(qCount, i2q, _, _) <- Afa.IORef.unseparateQTransitions qs2
  true <- Shaper.monadfn @buildTree STerm.LTrue
  hPutStrLn stderr "final3"
  let final3free = foldr -$ Pure true -$ [0 .. qCount - 1] $ \qi r ->
        Free $ STerm.And (Free $ STerm.Not $ Free $ STerm.State $ i2q qi) r
  final3 <- Shaper.Helpers.buildFree @buildD final3free
  hPutStrLn stderr "formatting"
  PrettyStranger2.formatIORef init3 final3 qs3

strangerToMachete :: IO ()
strangerToMachete = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init, final, qs) <- PrettyStranger2.parseIORef $ Stranger2.parseDefinitions $ T.pack txt
  Machete.formatIORef init final qs

strangerToPretty :: IO ()
strangerToPretty = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init, final, qs) <- PrettyStranger2.parseIORef $ Stranger2.parseDefinitions $ T.pack txt
  PrettyStranger2.formatIORef init final qs

removeFinalsPrettyMain ::
  forall d t r buildTree buildD q' v' r'.
  ( t ~ T.Text
  , q' ~ Finalful.SyncQs t
  , v' ~ Finalful.SyncVar t t
  , r' ~ Afa.IORef.Ref (STerm.Term q' v')
  , d ~ Afa.IORef.IORefRemoveFinalsD t t r r
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term q' v' r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
removeFinalsPrettyMain = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init2, final2, qs) <- PrettyStranger2.parseIORef $ PrettyStranger2.parseDefinitions $ T.pack txt
  hPutStrLn stderr "separating"
  Just qs1 <- Afa.IORef.trySeparateQTransitions qs
  hPutStrLn stderr "removing finals"
  (init3, qs2) <- Afa.IORef.removeFinalsHind init2 final2 qs1
  hPutStrLn stderr "unseparating"
  qs3@(qCount, i2q, _, _) <- Afa.IORef.unseparateQTransitions qs2
  true <- Shaper.monadfn @buildTree STerm.LTrue
  hPutStrLn stderr "final3"
  let final3free = foldr -$ Pure true -$ [0 .. qCount - 1] $ \qi r ->
        Free $ STerm.And (Free $ STerm.Not $ Free $ STerm.State $ i2q qi) r
  final3 <- Shaper.Helpers.buildFree @buildD final3free
  hPutStrLn stderr "formatting"
  PrettyStranger2.formatIORef init3 final3 qs3

removeFinalsNonsepMain ::
  forall d t r buildTree buildD q' v' r'.
  ( t ~ T.Text
  , q' ~ Finalful.SyncQs t
  , v' ~ Finalful.SyncVar t t
  , r' ~ Afa.IORef.Ref (STerm.Term q' v')
  , d ~ Afa.IORef.IORefRemoveFinalsD t t r r
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term q' v' r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
removeFinalsNonsepMain = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init2, final2, qs) <- PrettyStranger2.parseIORef $ PrettyStranger2.parseDefinitions $ T.pack txt
  hPutStrLn stderr "removing finals nonsep"
  (init2, qs2@(qCount, i2q, _, _)) <- Afa.IORef.removeFinals init2 final2 qs
  true <- Shaper.monadfn @buildTree STerm.LTrue
  hPutStrLn stderr "final3"
  let final2free = foldr -$ Pure true -$ [0 .. qCount - 1] $ \qi r ->
        Free $ STerm.And (Free $ STerm.Not $ Free $ STerm.State $ i2q qi) r
  final2 <- Shaper.Helpers.buildFree @buildD final2free
  hPutStrLn stderr "formatting"
  PrettyStranger2.formatIORef init2 final2 qs2

qdnfMain :: IO ()
qdnfMain = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init3, final3, qs) <- PrettyStranger2.parseIORef $ PrettyStranger2.parseDefinitions $ T.pack txt
  hPutStrLn stderr "separating"
  Just qs1 <- Afa.IORef.trySeparateQTransitions qs
  hPutStrLn stderr "toQDnf"
  qs2 <- Afa.IORef.toQDnf qs1
  hPutStrLn stderr "unseparating"
  qs3 <- Afa.IORef.unseparateQTransitions qs2
  hPutStrLn stderr "formatting"
  PrettyStranger2.formatIORef init3 final3 qs3

boomSeparateMain :: IO ()
boomSeparateMain = do
  txt <- getContents
  hPutStrLn stderr "parsing"
  (init2, final2, qs) <- PrettyStranger2.parseIORef $ PrettyStranger2.parseDefinitions $ T.pack txt
  hPutStrLn stderr "separating"
  qs1 <- Afa.IORef.boomSeparateQTransitions qs
  hPutStrLn stderr "unseparating"
  qs2 <- Afa.IORef.unseparateQTransitions qs1
  hPutStrLn stderr "formatting"
  PrettyStranger2.formatIORef init2 final2 qs2

range16ToPrettyRangeVarsMain ::
  forall d buildTree buildD r'.
  ( r' ~ Afa.IORef.Ref (STerm.Term Word32 Range16Nfa.Range16)
  , d ~ Afa.IORef.IORefRemoveFinalsD Void Void Void Void
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term Word32 Range16Nfa.Range16 r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
range16ToPrettyRangeVarsMain = do
  hPutStrLn stderr "parsing"
  nfa <- Range16Nfa.hReadNfaRaw stdin
  (init, finals, states) <- Range16Nfa.deserializeToIORef nfa
  hPutStrLn stderr "formatting"
  states'@(qCount, i2q, i2r, q2i) <- Afa.IORef.unseparateQTransitions states
  let nonfinals =
        accumArray (\_ _ -> False) True (0, qCount - 1) $
          map ((,()) . q2i) $ toList finals
  let nonfinals' =
        foldr (Fix .: STerm.And . Fix . STerm.Not . Fix . STerm.State . i2q) (Fix STerm.LTrue) $
          filter (nonfinals !) [0 .. qCount - 1]
  final' <- Shaper.Helpers.buildFix @buildD nonfinals'
  PrettyStranger2.formatIORef init final' states'

range16ToPrettyMain ::
  forall d buildTree buildD r'.
  ( r' ~ Afa.IORef.Ref (STerm.Term Word32 Range16Nfa.Range16)
  , d ~ Afa.IORef.IORefRemoveFinalsD Void Void Void Void
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term Word32 Range16Nfa.Range16 r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
range16ToPrettyMain = do
  hPutStrLn stderr "parsing"
  nfa <- Range16Nfa.hReadNfaRaw stdin
  (init1, finals, states@(qCount, i2q, _, q2i)) <- Range16Nfa.deserializeToIORef nfa
  hPutStrLn stderr "formatting"
  states1 <- Afa.IORef.unseparateQTransitions states
  let nonfinals =
        accumArray (\_ _ -> False) True (0, qCount - 1) $
          map ((,()) . q2i) $ toList finals
  let nonfinals' =
        foldr (Fix .: STerm.And . Fix . STerm.Not . Fix . STerm.State . i2q) (Fix STerm.LTrue) $
          filter (nonfinals !) [0 .. qCount - 1]
  final <- Shaper.Helpers.buildFix @buildD nonfinals'
  (init2, final2, states2) <- Range16Nfa.convertRangeIORef (init1, final, states1)
  PrettyStranger2.formatIORef init2 final2 states2

range16ToMacheteNfaMain :: IO ()
range16ToMacheteNfaMain = do
  hPutStrLn stderr "parsing"
  nfa <- Range16Nfa.hReadNfaRaw stdin
  Machete.formatRange16Nfa nfa

negateLang ::
  forall d buildTree buildD r'.
  ( r' ~ Afa.IORef.Ref (STerm.Term T.Text T.Text)
  , d ~ Afa.IORef.IORefRemoveFinalsD Void Void Void Void
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term T.Text T.Text r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
negateLang = do
  hPutStrLn stderr "parsing"
  txt <- TIO.hGetContents stdin
  (init, final, qs@(qCount, i2q, _, q2i)) <-
    PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  hPutStrLn stderr "splittingFinals"
  (nonfinals, Nothing) <- Afa.IORef.splitFinals final
  let finals = accumArray (\_ _ -> False) True (0, qCount - 1) $ map ((,()) . q2i) nonfinals
  let finals' = map i2q $ filter (finals !) [0 .. qCount - 1]
  hPutStrLn stderr "negating"
  (init1, finals1, states1@(qCount, i2q, i2r, q2i)) <- Afa.IORef.negateSeparated init finals' qs
  hPutStrLn stderr "formatting"
  let nonfinals =
        accumArray (\_ _ -> False) True (0, qCount - 1) $
          map ((,()) . q2i) $ toList finals1
  let nonfinals' =
        foldr (Fix .: STerm.And . Fix . STerm.Not . Fix . STerm.State . i2q) (Fix STerm.LTrue) $
          filter (nonfinals !) [0 .. qCount - 1]
  final' <- Shaper.Helpers.buildFix @buildD nonfinals'
  PrettyStranger2.formatIORef init1 final' states1

comboOp ::
  forall d t r buildTree buildD q' r' freeTerm.
  ( t ~ T.Text
  , d ~ Afa.IORef.IORefRemoveFinalsD Void Void Void Void
  , q' ~ Negate.Qombo t
  , r' ~ Afa.IORef.Ref (STerm.Term q' t)
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term q' t r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  , freeTerm ~ Free (STerm.Term q' t) r'
  ) =>
  ([freeTerm] -> freeTerm) ->
  [String] ->
  IO ()
comboOp op paths = do
  hPutStrLn stderr "parsing"
  afas <- for paths \path -> do
    f <- openFile path ReadMode
    txt <- TIO.hGetContents f
    (init, final, (qCount, i2q, i2r, q2i)) <-
      PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
    (nonfinals, Nothing) <- Afa.IORef.splitFinals final
    let finals = accumArray (\_ _ -> False) True (0, qCount - 1) $ map ((,()) . q2i) nonfinals
    let finals' = map i2q $ filter (finals !) [0 .. qCount - 1]
    return (init, finals', (qCount, i2q, Identity . i2r, q2i))
  (inits, finals, (qCount, i2q, i2r0, q2i)) <- Afa.IORef.qombo afas
  let i2r = runIdentity . i2r0
  let initFree = op (map Pure inits)
  init <- Shaper.Helpers.buildFree @buildD initFree
  let nonfinals =
        accumArray (\_ _ -> False) True (0, qCount - 1) $
          map ((,()) . q2i) $ toList finals
  let nonfinals' =
        foldr (Fix .: STerm.And . Fix . STerm.Not . Fix . STerm.State . i2q) (Fix STerm.LTrue) $
          filter (nonfinals !) [0 .. qCount - 1]
  final' <- Shaper.Helpers.buildFix @buildD nonfinals'
  PrettyStranger2.formatIORef init final' (qCount, i2q, i2r, q2i)

parseFormat :: IO ()
parseFormat = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  PrettyStranger2.formatIORef init final states

prettyToMachete :: IO ()
prettyToMachete = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  Machete.formatIORef init final states

prettyToSmv :: IO ()
prettyToSmv = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  Smv2.formatIORef init final states

prettyToMona :: IO ()
prettyToMona = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  Mona.formatIORef init final states

prettyToSeparated ::
  forall t d.
  ( t ~ T.Text
  , d ~ Afa.IORef.IORefRemoveFinalsD t t (Afa.IORef.Ref (STerm.Term t t)) Void
  ) =>
  IO ()
prettyToSeparated = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  Just states' <- Afa.IORef.trySeparateQTransitions states
  ([init', final'], states'') <- Negate.enum @d [init, final] states'
  Sep2.formatIORef init' final' states''

emailFilterBisim ::
  forall t d buildD buildTree q' r'.
  ( t ~ T.Text
  , d ~ Afa.IORef.IORefRemoveFinalsD t t (Afa.IORef.Ref (STerm.Term t t)) Void
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term q' t r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  , q' ~ Negate.Qombo t
  , r' ~ Afa.IORef.Ref (STerm.Term q' t)
  ) =>
  String ->
  String ->
  IO ()
emailFilterBisim path1 path2 = do
  [afa1, afa2] <- for [path1, path2] \path -> do
    f <- openFile path ReadMode
    txt <- TIO.hGetContents f
    (init, final, (qCount, i2q, i2r, q2i)) <-
      PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
    (nonfinals, Nothing) <- Afa.IORef.splitFinals final
    let finals = accumArray (\_ _ -> False) True (0, qCount - 1) $ map ((,()) . q2i) nonfinals
    let finals' = map i2q $ filter (finals !) [0 .. qCount - 1]
    return (init, finals', (qCount, i2q, Identity . i2r, q2i))
  ([init1, init2], finals, states@(qCount, i2q, i2r, q2i)) <- Afa.IORef.qombo [afa1, afa2]
  let initFree = Free $ STerm.And (Pure init1) (Pure init2)
  init <- Shaper.Helpers.buildFree @buildD initFree
  let nonfinals =
        accumArray (\_ _ -> False) True (0, qCount - 1) $
          map ((,()) . q2i) $ toList finals
  let nonfinals' =
        foldr (Fix .: STerm.And . Fix . STerm.Not . Fix . STerm.State . i2q) (Fix STerm.LTrue) $
          filter (nonfinals !) [0 .. qCount - 1]
  final <- Shaper.Helpers.buildFix @buildD nonfinals'

  Just states' <- Afa.IORef.trySeparateQTransitions (qCount, i2q, runIdentity . i2r, q2i)
  ([init1', init', final'], states'') <-
    Negate.enum
      @(TypeDict.Name "r" r' :+: TypeDict.Name "q" q' :+: d)
      [init1 :: r', init :: r', final :: r']
      states'
  Sep2.twoFormatIORef init1' final' init' final' states''

prettyToSeparatedMata :: IO ()
prettyToSeparatedMata = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  Just qs1 <- Afa.IORef.trySeparateQTransitions states
  Machete.formatSeparatedIORef init final qs1

prettyToSeparatedDnfMata ::
  forall d t r buildTree buildD.
  ( t ~ T.Text
  , r ~ Afa.IORef.Ref (STerm.Term t t)
  , d ~ Afa.IORef.IORefRemoveFinalsD t t r Void
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term t t r) r) [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  ) =>
  IO ()
prettyToSeparatedDnfMata = do
  txt <- TIO.getContents
  (init, final, states) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  Just states' <- Afa.IORef.trySeparateQTransitions states
  toDnf <- Negate.toDnf @d
  let sortCube :: [(Bool, Either t t)] -> Maybe [(Bool, Either t t)]
      sortCube elems =
        elemMap <&> sortBy compareElem . map (\(x, y) -> (y, x)) . HM.toList
        where
          elemMap = foldM step HM.empty elems
          step hm (sgn, qv) = HM.alterF -$ qv -$ hm $ \case
            Nothing -> Just (Just sgn)
            Just sgn0
              | sgn0 == sgn -> Just (Just sgn0)
              | otherwise -> Nothing
          compareElem (_, Left x) (_, Right y) = LT
          compareElem (_, Right x) (_, Left y) = GT
          compareElem (_, Left x) (_, Left y) = compareElem' x y
          compareElem (_, Right x) (_, Right y) = compareElem' x y
          compareElem' (T.unpack -> x) (T.unpack -> y) =
            case (readMaybe x, readMaybe y) of
              (Just (x :: Int), Just (y :: Int)) -> compare x y
              (Nothing, _) -> LT
              (_, Nothing) -> GT
  let buildCube :: [(Bool, Either t t)] -> IO r
      buildCube cube =
        Shaper.Helpers.buildFix @buildD $
          foldr (Fix .: STerm.And) (Fix STerm.LTrue) $
            cube <&> \(sgn, qv) ->
              (if sgn then id else Fix . STerm.Not)
                case qv of
                  Left q -> Fix (STerm.State q)
                  Right v -> Fix (STerm.Var v)
  let buildDisj cubes =
        Shaper.Helpers.buildFree @buildD $
          foldr (Free .: STerm.Or . Pure) (Free STerm.LFalse) cubes
  init'' <- toDnf init >>= mapM buildCube . mapMaybe sortCube >>= buildDisj
  final'' <- toDnf final >>= mapM buildCube . mapMaybe sortCube >>= buildDisj
  let (qCount, i2q, i2r, q2i) = states'
  i2r'' <-
    listArray (0, qCount - 1) <$> for [0 .. qCount - 1] \i -> do
      let transitions = i2r i
      concat <$> for transitions \(a, q) -> do
        aCubes <- toDnf a
        qCubes <- toDnf q
        aCubes' <- mapM buildCube $ mapMaybe sortCube aCubes
        qCubes' <- mapM buildCube $ mapMaybe sortCube qCubes
        return [(aCube, qCube) | aCube <- aCubes', qCube <- qCubes']

  Machete.formatSeparatedIORef init'' final'' (qCount, i2q, (i2r'' !), q2i)

prettyToAfasat :: IO ()
prettyToAfasat = do
  txt <- TIO.getContents
  let afa = PrettyStranger.parseAfa txt
  case simplifyAll afa of -- Afasat needs deLit and deUnary.
    Left solved -> hPutStrLn stderr ("solved " ++ show solved)
    Right afa' -> do
      hWriteCnfAfa (tseytin' $ reorderStates' afa') stdout

prettyToDot :: IO ()
prettyToDot = do
  txt <- TIO.getContents
  TIO.putStrLn $ toDot True $ PrettyStranger.parseAfa txt

prettySimplify1 :: IO ()
prettySimplify1 = do
  txt <- TIO.getContents
  let afa = PrettyStranger.parseAfa txt
  case simplifyAll afa of -- Afasat needs deLit and deUnary.
    Left solved -> hPutStrLn stderr ("solved " ++ show solved)
    Right afa' -> do
      TIO.putStrLn $ PrettyStranger.formatAfa afa'

prettyToSmv1 :: IO ()
prettyToSmv1 = do
  txt <- TIO.getContents
  TIO.putStrLn $ toSmv $ PrettyStranger.parseAfa txt

prettyToSmvReverseAsgn1 :: IO ()
prettyToSmvReverseAsgn1 = do
  txt <- TIO.getContents
  TIO.putStrLn $ toSmvReverseAssign $ PrettyStranger.parseAfa txt

prettyToSmvReverse1 :: IO ()
prettyToSmvReverse1 = do
  txt <- TIO.getContents
  TIO.putStrLn $ toSmvReverse $ PrettyStranger.parseAfa txt

prettyToPretty1 :: IO ()
prettyToPretty1 = do
  txt <- TIO.getContents
  TIO.putStrLn $ PrettyStranger.formatAfa $ PrettyStranger.parseAfa txt

treeReprUninit ::
  forall t d.
  ( t ~ T.Text
  , d ~ Afa.IORef.IORefRemoveFinalsD t t (Afa.IORef.Ref (STerm.Term t t)) Void
  ) =>
  IO ()
treeReprUninit = do
  hPutStrLn stderr "parsing"
  txt <- TIO.hGetContents stdin
  afa <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  afa' <- Negate.unInitState @d afa
  (init, final, states) <- Negate.unshare @d afa'
  PrettyStranger2.formatIORef init final states

treeRepr ::
  forall t d.
  ( t ~ T.Text
  , d ~ Afa.IORef.IORefRemoveFinalsD t t (Afa.IORef.Ref (STerm.Term t t)) Void
  ) =>
  IO ()
treeRepr = do
  hPutStrLn stderr "parsing"
  txt <- TIO.hGetContents stdin
  afa <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  (init, final, states) <- Negate.unshare @d afa
  PrettyStranger2.formatIORef init final states

emailFilterAda ::
  forall d buildTree buildD buildTree2 buildD2 r' r'2.
  ( r' ~ Afa.IORef.Ref (STerm.Term (Negate.Qombo Word32) Range16Nfa.Range16)
  , r'2 ~ Afa.IORef.Ref (STerm.Term (Negate.Qombo (Negate.Qombo Word32)) Range16Nfa.Range16)
  , d ~ Afa.IORef.IORefRemoveFinalsD Void Void Void Void
  , buildTree ~ Shaper.Mk (Shaper.MfnK (STerm.Term (Negate.Qombo Word32) Range16Nfa.Range16 r') r') [d|buildTree|]
  , buildD ~ (TypeDict.Name "build" buildTree :+: d)
  , buildTree2 ~ Shaper.Mk (Shaper.MfnK (STerm.Term (Negate.Qombo (Negate.Qombo Word32)) Range16Nfa.Range16 r'2) r'2) [d|buildTree|]
  , buildD2 ~ (TypeDict.Name "build" buildTree2 :+: d)
  ) =>
  Int ->
  [String] ->
  IO ()
emailFilterAda nSplitAt paths = do
  let (paths1, paths2) = splitAt nSplitAt paths
  let wrap (qCount, i2q, i2r, q2i) = (qCount, i2q, Identity . i2r, q2i)
  let unwrap (qCount, i2q, i2r, q2i) = (qCount, i2q, runIdentity . i2r, q2i)
  [nfas1, nfas2] <- for [paths1, paths2] \paths -> for paths \path -> do
    f <- openFile path ReadMode
    nfa <- Range16Nfa.hReadNfaRaw f
    (init1, finals, states) <- Range16Nfa.deserializeToIORef nfa
    states' <- Afa.IORef.unseparateQTransitions states
    return (init1, finals, wrap states')

  (inits1, finals1, qs1) <- Afa.IORef.qombo nfas1
  let initFree1 = foldr1 (Free .: STerm.And) (map Pure inits1)
  init1 <- Shaper.Helpers.buildFree @buildD initFree1

  (inits2, finals2, qs2) <- Afa.IORef.qombo nfas2
  let initFree2 = foldr1 (Free .: STerm.And) (map Pure inits2)
  init2 <- Shaper.Helpers.buildFree @buildD initFree2

  (init2', finals2', qs2') <- Afa.IORef.negateSeparated init2 finals2 (unwrap qs2)

  ([init31, init32], finals3, qs3) <-
    Afa.IORef.qombo [(init1, finals1, qs1), (init2', finals2', wrap qs2')]
  let initFree3 = Free $ STerm.And (Pure init31) (Pure init32)
  init3 <- Shaper.Helpers.buildFree @buildD2 initFree3

  Ada2.formatIORef init3 finals3 (unwrap qs3)

prettyToAda :: IO ()
prettyToAda = do
  txt <- TIO.getContents
  (init, final, states@(qCount, i2q, i2r, q2i)) <- PrettyStranger2.parseIORef (PrettyStranger2.parseDefinitions txt)
  (nonfinals, Nothing) <- Afa.IORef.splitFinals final
  let finals = accumArray (\_ _ -> False) True (0, qCount - 1) $ map ((,()) . q2i) nonfinals
  let finals' = map i2q $ filter (finals !) [0 .. qCount - 1]
  AdaBits.formatIORef init finals' states

newtype Both a = Both {unBoth :: (a, a)}

instance Functor Both where
  fmap f (Both (x, y)) = Both (f x, f y)

instance Foldable Both where
  foldMap f (Both (x, y)) = f x <> f y

instance Traversable Both where
  traverse f (Both (x, y)) = Both .: (,) <$> f x <*> f y

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["strangerToMachete"] -> strangerToMachete
    ["strangerToPretty"] -> strangerToPretty
    ["strangerRemoveFinals"] -> removeFinalsMain
    ["removeFinals"] -> removeFinalsPrettyMain
    ["removeFinalsNonsep"] -> removeFinalsNonsepMain
    ["qdnf"] -> qdnfMain
    ["boomSeparate"] -> boomSeparateMain
    ["range16ToPrettyRangeVars"] -> range16ToPrettyRangeVarsMain
    ["range16ToPretty"] -> range16ToPrettyMain
    ["parseFormat"] -> parseFormat
    ["negate"] -> negateLang
    ("and" : paths) -> comboOp (foldr1 $ Free .: STerm.And) paths
    ("or" : paths) -> comboOp (foldr1 $ Free .: STerm.Or) paths
    ("neq" : paths) -> (`comboOp` paths) \[a, b, na, nb] ->
      Free $ STerm.Or (Free $ STerm.And a nb) (Free $ STerm.And na b)
    ("emailFilterAda" : nSplitAt : paths) -> emailFilterAda (read nSplitAt) paths
    ["treeRepr"] -> treeRepr
    ["treeReprUninit"] -> treeReprUninit
    ["range16ToMacheteNfa"] -> range16ToMacheteNfaMain
    ["prettyToAda"] -> prettyToAda
    ["prettyToMachete"] -> prettyToMachete
    ["prettyToSeparatedMata"] -> prettyToSeparatedMata
    ["prettyToSeparatedDnfMata"] -> prettyToSeparatedDnfMata
    ["prettyToSmv"] -> prettyToSmv
    ["prettyToSmv1"] -> prettyToSmv1
    ["prettyToSmvReverse1"] -> prettyToSmvReverse1
    ["prettyToSmvReverseAsgn1"] -> prettyToSmvReverseAsgn1
    ["prettyToMona"] -> prettyToMona
    ["prettyToAfasat"] -> prettyToAfasat
    ["prettyToDot"] -> prettyToDot
    ["prettySimplify1"] -> prettySimplify1
    ["prettyToPretty1"] -> prettyToPretty1
    ["prettyToSeparated"] -> prettyToSeparated
    ["emailFilterBisim", path1, path2] -> emailFilterBisim path1 path2
    _ -> do
      (Opts readers writers) <-
        execParser $
          info (optParser <**> helper) $
            fullDesc
              <> progDesc
                "Convert LTLe to a symbolic alternating finite automaton, possibly \
                \preprocess the automaton and output it somewhere further."
              <> header "ltle-to-afa: symbolic alternating finite automata preprocessing"

      applyWritersAndReaders writers readers

applyWritersAndReaders (writer : writers) (Fix (Compose action)) =
  action >>= \case
    Nil -> return ()
    Cons (name, bafa) readers' -> do
      tic <- getPOSIXTime
      finishedVar <- registerDelay timeoutMicro
      resultVar <- newTVarIO Nothing
      threadId <- forkIO $
        case writer name bafa of
          Left result -> do
            atomically $ do
              writeTVar finishedVar True
              writeTVar resultVar $ Just $ Left result
          Right (sizes, write) -> do
            write
            atomically $ do
              writeTVar finishedVar True
              writeTVar resultVar $ Just $ Right sizes

      mresult <-
        atomically $
          readTVar finishedVar >>= \case
            False -> retry
            _ -> readTVar resultVar

      toc <- getPOSIXTime

      when (isNothing mresult) $ killThread threadId

      let (qCount, nodeCount, edgeCount, result) = case mresult of
            Nothing -> (0, 0, 0, -2)
            Just (Left result) -> (0, 0, 0, if result then 1 else 0)
            Just (Right (qCount, nCount, eCount)) -> (qCount, nCount, eCount, -1)

      putStrLn $
        intercalate
          "\t"
          [ name
          , show $ floor $ 1000 * (toc - tic)
          , show qCount
          , show nodeCount
          , show edgeCount
          , show result
          ]

      hFlush stdout

      applyWritersAndReaders writers readers'
applyWritersAndReaders _ (Fix (Compose action)) = error "writers exhausted"
