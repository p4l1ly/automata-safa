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

module Afa.Convert.Machete where

import qualified Afa.Convert.PrettyStranger2 as Pretty
import Afa.Finalful
import Afa.Finalful.STerm (Term (..))
import Afa.IORef
import Afa.Lib (listArray')
import Afa.Negate (Qombo (Qombo))
import qualified Capnp.Gen.Afa.Model.Separated.Pure as AfaC
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Control.Applicative
import Control.Lens (itraverse, (&))
import Control.Monad.Free
import Control.Monad.State.Strict
import Control.Monad.Trans (lift)
import Data.Array
import Data.Attoparsec.Expr
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
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
import Data.Word
import Debug.Trace
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Lift (Inc, K (K), LiftCount, Unwrap)
import Shaper
import Shaper.Helpers (BuildD, buildFree)
import TypeDict

type FormatFormulaD d m =
  FormatFormulaD_ d m (FormatFormulaA d (Term [g|q|] [g|v|] [g|r|]) [g|r|]) [g|q|] [g|v|] [g|r|]
type FormatFormulaA (d :: TypeDict) x r =
  FormatFormulaA1
    ( Name "recur" (MkN (RecK r x T.Text) [d|any|])
        :+: Name "deref" (Mk (MfnK r (Term [g|q|] [g|v|] [g|r|])) [d|deref|])
        :+: Name "refIsTree" (Mk (MfnK r Bool) [d|refIsTree|])
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
    :|: D.Name "refIsTree" (MonadFn [d'|refIsTree|] m)
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
          True -> contents
          False -> do
            txt <- contents
            fIx <- lift $ readIORef vFIx
            lift $ writeIORef vFIx $ fIx + 1
            lift $ modifyIORef stack ((fIx, txt) :)
            return $ do T.cons 'n' (T.pack (show fIx))
        where
          contents =
            case x of
              LTrue -> return "true"
              LFalse -> return "false"
              State q -> return $ T.cons 'q' (showT q)
              Var v -> return $ T.cons 'a' (showT v)
              Not !r -> do
                !r' <- rec r
                monadfn @(Inc [d'|refIsTree|]) r >>= \case
                  True ->
                    monadfn @(Inc [d'|deref|]) r <&> \case
                      And _ _ -> T.concat ["!(", r', ")"]
                      Or _ _ -> T.concat ["!(", r', ")"]
                      _ -> T.cons '!' r'
                  False -> return $ T.cons '!' r'
              And !a !b -> do
                !a' <- rec a
                !b' <- rec b
                a'' <-
                  monadfn @(Inc [d'|refIsTree|]) a >>= \case
                    True -> do
                      monadfn @(Inc [d'|deref|]) a <&> \case
                        Or _ _ -> T.concat ["(", a', ")"]
                        _ -> a'
                    False -> return a'
                b'' <-
                  monadfn @(Inc [d'|refIsTree|]) b >>= \case
                    True ->
                      monadfn @(Inc [d'|deref|]) b <&> \case
                        Or _ _ -> T.concat ["(", b', ")"]
                        _ -> b'
                    False -> return b'
                return $ T.concat [a'', " & ", b'']
              Or !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- monadfn @(Inc [d'|deref|]) a
                bt <- monadfn @(Inc [d'|deref|]) b
                a'' <-
                  monadfn @(Inc [d'|refIsTree|]) a >>= \case
                    True -> do
                      monadfn @(Inc [d'|deref|]) a <&> \case
                        And _ _ -> T.concat ["(", a', ")"]
                        _ -> a'
                    False -> return a'
                b'' <-
                  monadfn @(Inc [d'|refIsTree|]) b >>= \case
                    True ->
                      monadfn @(Inc [d'|deref|]) b <&> \case
                        And _ _ -> T.concat ["(", b', ")"]
                        _ -> b'
                    False -> return b'
                return $ T.concat [a'', " | ", b'']
          contents2 =
            case x of
              LTrue -> return "true"
              LFalse -> return "false"
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

  convert <- recur @ [d'|recur|] algebra
  return (convert, readIORef stack)

format ::
  forall d q v r.
  D.ToConstraint (FormatFormulaD d IO) =>
  [g|r|] ->
  [g|r|] ->
  (Int, Int -> [g|q|], Int -> [g|r|], [g|q|] -> Int) ->
  IO ()
format init final (qCount, i2q, i2r, q2i) = do
  (convert, getShared) <- formatFormula @d

  TIO.putStr "%Initial "
  TIO.putStrLn =<< convert init
  TIO.putStr "%Final "
  TIO.putStrLn =<< convert final
  for_ [0 .. qCount - 1] \i -> do
    TIO.putStr "q"
    TIO.putStr (showT $ i2q i)
    TIO.putStr " "
    TIO.putStrLn =<< convert (i2r i)

  getShared >>= mapM_ \(i, txt) -> do
    TIO.putStr "n"
    putStr (show i)
    TIO.putStr " "
    TIO.putStrLn txt

formatIORef ::
  forall q v r r' d result.
  ( r ~ Afa.IORef.Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , ShowT q
  , ShowT v
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  IO ()
formatIORef = Afa.Convert.Machete.format @d

class ShowT a where
  showT :: a -> T.Text

instance ShowT T.Text where
  showT = id

instance ShowT Word32 where
  showT = T.pack . show

instance ShowT Word8 where
  showT = T.pack . show

instance ShowT AfaC.Range16 where
  showT (AfaC.Range16 a b) = [i|"[#{a}-#{b}]"|]

instance ShowT q => ShowT (SyncQs q) where
  showT (QState q) = [i|Q#{showT q}|]
  showT SyncState = "Sync"

instance (ShowT q, ShowT v) => ShowT (SyncVar q v) where
  showT (VVar v) = [i|V#{showT v}|]
  showT (QVar v) = [i|Q#{showT v}|]
  showT FVar = "F"

instance ShowT q => ShowT (Qombo q) where
  showT (Qombo n q) = [i|C#{n}_#{showT q}|]

decodeChar :: Word16 -> T.Text
decodeChar w = case toEnum $ fromEnum w of
  '\\' -> "\\\\"
  '"' -> "\\\""
  '-' -> "\\-"
  ' ' -> " "
  '\t' -> "\\t"
  '\n' -> "\\n"
  '\r' -> "\\r"
  '\f' -> "\\f"
  '\v' -> "\\v"
  '\a' -> "\\a"
  c
    | isSpace c -> [i|\\u{#{w}}|]
    | isPrint c -> T.singleton c
    | otherwise -> [i|\\u{#{w}}|]

formatRange16Nfa :: AfaC.Range16Nfa -> IO ()
formatRange16Nfa (AfaC.Range16Nfa states initial finals) = do
  TIO.putStrLn [i|%InitialStates q#{initial}|]
  let finalMask =
        accumArray (\_ _ -> True) False (0, fromIntegral (V.length states - 1)) $
          map (,()) $ toList finals
  let finals' = filter (finalMask !) (range $ bounds finalMask)
  let finals''
        | V.length states == 0 = ""
        | otherwise = T.intercalate " " $ finals' <&> \q -> [i|q#{q}|]
  TIO.putStrLn [i|%FinalStates #{finals''}|]
  states & itraverse \qi ts ->
    for ts \(AfaC.ConjunctR16Q ranges qi') -> do
      let ranges' =
            T.concat . toList $
              ranges <&> \case
                (AfaC.Range16 a b)
                  | a == b -> [i|#{decodeChar a}|]
                  | otherwise -> [i|#{decodeChar a}-#{decodeChar b}|]
      TIO.putStrLn [i|q#{qi} "#{ranges'}" q#{qi'}|]
  return ()

formatSeparated ::
  forall d q v r deref.
  ( D.ToConstraint (FormatFormulaD d IO)
  , deref ~ Mk (MfnK [g|r|] (Term [g|q|] [g|v|] [g|r|])) [d|deref|]
  , MonadFn deref IO
  ) =>
  [g|r|] ->
  [g|r|] ->
  (Int, Int -> [g|q|], Int -> [([g|r|], [g|r|])], [g|q|] -> Int) ->
  IO ()
formatSeparated init final (qCount, i2q, i2r, q2i) = do
  (convert, getShared) <- formatFormula @d

  TIO.putStr "%Initial "
  TIO.putStrLn =<< convert init
  TIO.putStr "%Final "
  TIO.putStrLn =<< convert final
  for_ [0 .. qCount - 1] \i -> do
    let qtxt = showT $ i2q i
    for_ (i2r i) \(aterm, qterm) -> do
      TIO.putStr "q"
      TIO.putStr qtxt
      TIO.putStr " "
      aterm' <- convert aterm
      qterm' <- convert qterm
      let notNullary = \case
            LTrue -> False
            LFalse -> False
            State get -> False
            Var get -> False
            Not get -> True
            And get get' -> True
            Or get get' -> True
      aParen <- monadfn @deref aterm <&> notNullary
      if aParen
        then do
          TIO.putStr "("
          TIO.putStr aterm'
          TIO.putStr ")"
        else TIO.putStr aterm'
      TIO.putStr " "
      qParen <- monadfn @deref qterm <&> notNullary
      if qParen
        then do
          TIO.putStr "("
          TIO.putStr qterm'
          TIO.putStrLn ")"
        else TIO.putStrLn qterm'

  getShared >>= mapM_ \(i, txt) -> do
    TIO.putStr "n"
    putStr (show i)
    TIO.putStr " "
    TIO.putStrLn txt

formatSeparatedIORef ::
  forall q v r r' d result.
  ( r ~ Afa.IORef.Ref (Term q v)
  , d ~ IORefRemoveFinalsD q v r r'
  , ShowT q
  , ShowT v
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> [(r, r)], q -> Int) ->
  IO ()
formatSeparatedIORef = Afa.Convert.Machete.formatSeparated @d

parseWhole :: Parser a -> T.Text -> a
parseWhole parser str = case Parsec.parse parser str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseDefinitions :: T.Text -> [Pretty.Definition]
parseDefinitions str =
  flip mapMaybe rows \row ->
    case T.uncons row of
      Just ('#', _) -> Nothing
      Nothing -> Nothing
      Just _ ->
        let (header, T.uncons -> Just (' ', contents)) = T.break (== ' ') row
         in Just $ parseOne header (unspace contents)
  where
    unspace = T.filter (not . isSpace)
    rows = T.lines str

parseOne :: T.Text -> T.Text -> Pretty.Definition
parseOne name value = case T.uncons name of
  Just ('n', name') -> Pretty.DFormula name' $ parseWhole expr value
  Just ('q', name') -> Pretty.DState name' $ parseWhole expr value
  Just ('%', keyword) -> case keyword of
    "Initial" -> Pretty.DInitialStates $ parseWhole expr value
    "Final" -> Pretty.DFinalStates $ parseWhole expr value
    _ -> error [i|unknown keyword #{keyword}|]
  Just (t, _) -> error [i|unknown type #{t}|]
  Nothing -> error "empty identifier"

expr :: Parser Pretty.STermStr
expr = buildExpressionParser table term <?> "expression"
  where
    table =
      [ [Infix (Free .: And <$ char '&') AssocLeft]
      , [Infix (Free .: Or <$ char '|') AssocLeft]
      ]

identifier :: Parser T.Text
identifier = Parsec.takeWhile (\case '_' -> True; '\'' -> True; x -> isAlphaNum x)

term :: Parser Pretty.STermStr
term =
  "(" *> expr <* ")"
    <|> (Free . Not <$> (char '!' *> term))
    <|> (Free . State <$> ("q" *> identifier))
    <|> (Pure <$> ("n" *> identifier))
    <|> (Free LTrue <$ "true")
    <|> (Free LFalse <$ "false")
    <|> (Free . Var <$> ("a" *> identifier))
    <?> "expected a term"
