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

type Qs r = StateHashMap T.Text r

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
              LTrueMulti -> return "kTrue"
              LFalseMulti -> return "kFalse"
              StateMulti q -> return $ T.cons 's' (identify q)
              VarMulti v -> return $ T.cons 'a' (identify v)
              NotMulti !r -> do
                T.cons '!' <$> rec r
              AndMulti xs -> do
                !xs' <- mapM rec xs
                return $ T.concat ["(", T.intercalate " & " xs', ")"]
              OrMulti xs -> do
                !xs' <- mapM rec xs
                return $ T.concat ["(", T.intercalate " | " xs', ")"]

  return (R.runRecur @[g1|rec|] algebra, readIORef stack)

unparen :: T.Text -> T.Text
unparen t = case T.uncons t of
  Just ('(', t') -> T.init t'
  _ -> t


type PrintD d = (FormatFormulaD d, States $qs $q $r) :: Constraint

hPrint :: forall d. PrintD d => Handle -> ($r, $r, $qs) -> IO ()
hPrint h (init, final, qs) = do
  (runConvert, getShared) <- formatFormula @d

  runConvert \convert -> do
    lift $ TIO.hPutStr h "@kInitialFormula: "
    lift . TIO.hPutStrLn h . unparen =<< convert init
    lift $ TIO.hPutStr h "@kFinalFormula: "
    lift . TIO.hPutStrLn h . unparen =<< convert final
    for_ (stateList qs) \(q, r) -> do
      lift $ TIO.hPutStr h "@s"
      lift $ TIO.hPutStr h (identify q)
      lift $ TIO.hPutStr h ": "
      lift . TIO.hPutStrLn h . unparen =<< convert r

  getShared >>= mapM_ \(i, txt) -> do
    TIO.hPutStr h "@f"
    System.IO.hPutStr h (show i)
    TIO.hPutStr h ": "
    TIO.hPutStrLn h $ unparen txt

print :: forall d. PrintD d => ($r, $r, $qs) -> IO ()
print = hPrint @d stdout
