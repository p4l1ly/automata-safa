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

module Afa.Convert.PrettyStranger where

import Data.Array
import Afa.Convert.Identifier
import Afa.IORef
import Afa.Lib
import Afa.Term (Term (..), q, r, v)
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
import Data.Monoid
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Traversable
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import qualified InversionOfControl.Recur as R
import InversionOfControl.TypeDict
import Afa.States

parseWhole :: Parser a -> T.Text -> a
parseWhole parser str = case Parsec.parse parser str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseDefinitions :: T.Text -> [AfaDefinition]
parseDefinitions str = parseWhole (many defParser) str'
  where
    str' = T.filter (not . isSpace) str
    defParser =
      parseOne
        <$> (char '@' *> Parsec.takeWhile (/= ':') <* char ':')
        <*> Parsec.takeWhile (/= '@')

type ParseD d = Follow (ParseI d (ParseA d $r) $r) :: TypeDict

data ParseA d r
type instance Definition (ParseA d r) =
  Name "share" (Inherit (Explicit r r) [k|share|])
    :+: Name "build" (Inherit (Explicit [g|term|] r) [k|build|])
    :+: End

data ParseI d d1 r
type instance Definition (ParseI d d1 r) =
  Name "all"
    ( d1 ~ ParseA d r
    , Term T.Text T.Text r ~ [g|term|]
    , MonadFn [g1|share|] IO
    , MonadFn [g1|build|] IO
    )
    :+: End

parse ::
  forall d r d1.
  (ToConstraint (Follow (ParseI d d1 r))) =>
  [AfaDefinition] ->
  IO (r, r, StateHashMap T.Text r)
parse (groupDefs -> (init, final, formulae, states)) = do
  sharedsRef  <- newIORef HM.empty

  let convert :: TxtTerm -> IO r
      convert f = mapM fRec f >>= buildFree @[g1|build|]

      fRec :: T.Text -> IO r
      fRec name = do
        shareds <- readIORef sharedsRef
        case shareds HM.!? name of
          Just Nothing -> error $ "cycle " ++ T.unpack name
          Just (Just r) -> return r
          Nothing -> do
            writeIORef sharedsRef $ HM.insert name Nothing shareds
            f <- mapM fRec (formulae HM.! name)
            r <- buildFree @[g1|build|] f >>= monadfn @[g1|share|]
            modifyIORef sharedsRef $ HM.insert name (Just r)
            return r

  initR <- convert init
  finalR <- convert final
  stateRs <- mapM convert states

  return (initR, finalR, StateHashMap stateRs)

type TxtTerm = Free (Term T.Text T.Text) T.Text

data AfaDefinition
  = DInitialStates {dterm :: TxtTerm}
  | DFinalStates {dterm :: TxtTerm}
  | DFormula {name :: T.Text, dterm :: TxtTerm}
  | DState {name :: T.Text, dterm :: TxtTerm}
  deriving (Show)

parseOne :: T.Text -> T.Text -> AfaDefinition
parseOne name value = case T.uncons name of
  Just ('f', name') -> DFormula name' $ parseWhole expr value
  Just ('s', name') -> DState name' $ parseWhole expr value
  Just ('k', keyword) -> case keyword of
    "InitialFormula" -> DInitialStates $ parseWhole expr value
    "FinalFormula" -> DFinalStates $ parseWhole expr value
    _ -> error [i|unknown keyword #{keyword}|]
  Just (t, _) -> error [i|unknown type #{t}|]
  Nothing -> error "empty identifier"

expr :: Parser TxtTerm
expr = buildExpressionParser table term <?> "expression"
  where
    table =
      [ [Infix (Free .: And <$ char '&') AssocLeft]
      , [Infix (Free .: Or <$ char '|') AssocLeft]
      ]

identifier :: Parser T.Text
identifier = Parsec.takeWhile (\case '_' -> True; x -> isAlphaNum x)

term :: Parser TxtTerm
term =
  "(" *> expr <* ")"
    <|> (Free . Not <$> (char '!' *> term))
    <|> (Free . State <$> ("s" *> identifier))
    <|> (Pure <$> ("f" *> identifier))
    <|> (Free LTrue <$ "kTrue")
    <|> (Free LFalse <$ "kFalse")
    <|> (Free . Var <$> ("a" *> identifier))
    <?> "expected a term"

groupDefs ::
  [AfaDefinition] ->
  ( TxtTerm
  , TxtTerm
  , HM.HashMap T.Text TxtTerm
  , HM.HashMap T.Text TxtTerm
  )
groupDefs defs =
  ( case appEndo init [] of [x] -> x; _ -> error "expected single kInitialFormula"
  , case appEndo final [] of [x] -> x; _ -> error "expected single kFinalFormula"
  , HM.fromListWithKey
      (\k _ _ -> error $ "multiple definitions of f" ++ T.unpack k)
      (appEndo formulae [])
  , HM.fromListWithKey
      (\k _ _ -> error $ "multiple definitions of s" ++ T.unpack k)
      (appEndo states [])
  )
  where
    (init, final, states, formulae) = execWriter $
      for defs $ \case
        DFormula name dterm -> tell (mempty, mempty, mempty, Endo ((name, dterm) :))
        DState name dterm -> tell (mempty, mempty, Endo ((name, dterm) :), mempty)
        DInitialStates dterm -> tell (Endo (dterm :), mempty, mempty, mempty)
        DFinalStates dterm -> tell (mempty, Endo (dterm :), mempty, mempty)

type FormatFormulaD d =
  Follow (FormatFormulaI d (FormatFormulaA d $r) $q $v $r) :: TypeDict

data FormatFormulaA d r
type instance Definition (FormatFormulaA d r) =
  Name "deref" (Inherit (Explicit r [g|term|]) [k|deref|])
    :+: Name "isTree" (Inherit (Explicit r Bool) [k|isTree|])
    :+: Name "rec" (R.Explicit [k|rcata|] Zero r (r, [g|term|]))
    :+: End

data FormatFormulaI d d1 q v r
type instance Definition (FormatFormulaI d d1 q v r) =
  Name "all"
    ( d1 ~ FormatFormulaA d r
    , Term q v r ~ [g|term|]
    , Identify q
    , Identify v
    , MonadFn [g1|deref|] IO
    , MonadFn [g1|isTree|] IO
    , R.Recur [g1|rec|] T.Text IO
    )
    :+: End
formatFormula ::
  forall d d1 q v r t a.
  ( ToConstraint (Follow (FormatFormulaI d d1 q v r))
  , t ~ R.Et [g1|rec|]
  ) =>
  IO
    ( ((r -> t IO T.Text) -> t IO a) -> IO a
    , IO [(Int, T.Text)]
    )
formatFormula = do
  vFIx <- newIORef (0 :: Int)
  stack <- newIORef ([] :: [(Int, T.Text)])

  let algebra :: (r -> t IO T.Text) -> (r, [g|term|]) -> t IO T.Text
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
              LTrue -> return "kTrue"
              LFalse -> return "kFalse"
              State q -> return $ T.cons 's' (identify q)
              Var v -> return $ T.cons 'a' (identify v)
              Not !r -> do
                !r' <- rec r
                lift (monadfn @[g1|isTree|] r) >>= \case
                  True ->
                    lift (monadfn @[g1|deref|] r) <&> \case
                      And _ _ -> T.concat ["!(", r', ")"]
                      Or _ _ -> T.concat ["!(", r', ")"]
                      _ -> T.cons '!' r'
                  False -> return $ T.cons '!' r'
              And !a !b -> do
                !a' <- rec a
                !b' <- rec b
                a'' <-
                  lift (monadfn @[g1|isTree|] a) >>= \case
                    True -> do
                      lift (monadfn @[g1|deref|] a) <&> \case
                        Or _ _ -> T.concat ["(", a', ")"]
                        _ -> a'
                    False -> return a'
                b'' <-
                  lift (monadfn @[g1|isTree|] b) >>= \case
                    True ->
                      lift (monadfn @[g1|deref|] b) <&> \case
                        Or _ _ -> T.concat ["(", b', ")"]
                        _ -> b'
                    False -> return b'
                return $ T.concat [a'', " & ", b'']
              Or !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- lift $ monadfn @[g1|deref|] a
                bt <- lift $ monadfn @[g1|deref|] b
                a'' <-
                  lift (monadfn @[g1|isTree|] a) >>= \case
                    True -> do
                      lift (monadfn @[g1|deref|] a) <&> \case
                        And _ _ -> T.concat ["(", a', ")"]
                        _ -> a'
                    False -> return a'
                b'' <-
                  lift (monadfn @[g1|isTree|] b) >>= \case
                    True ->
                      lift (monadfn @[g1|deref|] b) <&> \case
                        And _ _ -> T.concat ["(", b', ")"]
                        _ -> b'
                    False -> return b'
                return $ T.concat [a'', " | ", b'']

  return (R.runRecur @[g1|rec|] algebra, readIORef stack)

format ::
  forall d q v r d1 qs.
  ( Term q v r ~ [g|term|]
  , ToConstraint (FormatFormulaD d)
  , States qs q r
  ) =>
  (r, r, qs) -> IO ()
format (init, final, qs) = do
  (runConvert, getShared) <- formatFormula @d

  runConvert \convert -> do
    lift $ TIO.putStr "@kInitialFormula: "
    lift . TIO.putStrLn =<< convert init
    lift $ TIO.putStr "@kFinalFormula: "
    lift . TIO.putStrLn =<< convert final
    for_ (stateList qs) \(q, r) -> do
      lift $ TIO.putStr "@s"
      lift $ TIO.putStr (identify q)
      lift $ TIO.putStr ": "
      lift . TIO.putStrLn =<< convert r

  getShared >>= mapM_ \(i, txt) -> do
    TIO.putStr "@f"
    putStr (show i)
    TIO.putStr ": "
    TIO.putStrLn txt
