{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
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

module Afa.Convert.PrettyStranger2 where

import Afa.Finalful.STerm (Term (..))
import Afa.IORef
import Afa.Lib (listArray')
import Control.Applicative
import Control.Monad.Free
import Control.Monad.State.Strict
import Control.Monad.Trans (lift)
import Control.Monad.Writer.Strict
import Data.Array
import Data.Attoparsec.Expr
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
import Data.Char
import Data.Composition ((.:))
import qualified Data.HashMap.Strict as HM
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo (..))
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Data.Traversable
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Lift (Inc, K (K), LiftCount, Unwrap)
import Shaper
import Shaper.Helpers (BuildD, buildFree)
import TypeDict

parseWhole :: Parser a -> T.Text -> a
parseWhole parser str = case Parsec.parse parser str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseDefinitions :: T.Text -> [Definition]
parseDefinitions str = parseWhole parser str'
  where
    str' = T.filter (not . isSpace) str
    parser =
      many $
        parseOne
          <$> (char '@' *> Parsec.takeWhile (/= ':') <* char ':')
          <*> Parsec.takeWhile (/= '@')

type ParseD d m = ParseD_ d m (ParseA d [g|r|]) [g|r|]
type ParseA d r =
  Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
    :+: Name "buildTreeD" (Name "build" (Mk (MfnK (Term T.Text T.Text r) r) [d|buildTree|]) :+: d)
    :+: End
type ParseD_ (d :: TypeDict) (m :: * -> *) (d' :: TypeDict) (r :: *) =
  D.Name "aliases" (r ~ [g|r|], d' ~ ParseA d r)
    :|: D.Name "" (MonadFn [d'|shareTree|] m)
    :|: D.Name "" (BuildD [g'|buildTreeD|] (Term T.Text T.Text) r m)
    :|: D.End
parse ::
  forall d m r d'.
  ( D.ToConstraint (ParseD_ d m d' r)
  ) =>
  T.Text ->
  m (r, r, (Int, Int -> T.Text, Int -> r, T.Text -> Int))
parse str = do
  (initR, finalR, stateRs) <- flip evalStateT HM.empty $ do
    (,,) <$> convert init <*> convert final <*> mapM convert states
  let stateList = HM.toList stateRs
      arr = listArray (0, HM.size stateRs - 1) stateList
      stateNames = map fst stateList
      state2ix = HM.fromList $ zip stateNames [0 ..]
      states = (rangeSize $ bounds arr, fst . (arr !), snd . (arr !), (state2ix HM.!))
  return (initR, finalR, states)
  where
    (init, final, formulae, states) = orize $ parseDefinitions str
    convert :: Free (Term T.Text T.Text) T.Text -> StateT (HM.HashMap T.Text (Maybe r)) m r
    convert f = mapM fRec f >>= buildFree @(LiftTags [g'|buildTreeD|])
    fRec :: T.Text -> StateT (HM.HashMap T.Text (Maybe r)) m r
    fRec name =
      gets (HM.!? name) >>= \case
        Just Nothing -> error $ "cycle " ++ T.unpack name
        Just (Just r) -> return r
        Nothing -> do
          modify $ HM.insert name Nothing
          (f :: Free (Term T.Text T.Text) r) <- mapM fRec (formulae HM.! name)
          buildFree @(LiftTags [g'|buildTreeD|]) f >>= monadfn @(Inc [d'|shareTree|])

type STermStr = Free (Term T.Text T.Text) T.Text

data Definition
  = DInitialStates {dterm :: STermStr}
  | DFinalStates {dterm :: STermStr}
  | DFormula {name :: T.Text, dterm :: STermStr}
  | DState {name :: T.Text, dterm :: STermStr}

parseOne :: T.Text -> T.Text -> Definition
parseOne name value = case T.uncons name of
  Just ('f', name') -> DFormula name' $ parseWhole expr value
  Just ('s', name') -> DState name' $ parseWhole expr value
  Just ('k', keyword) -> case keyword of
    "InitialFormula" -> DInitialStates $ parseWhole expr value
    "FinalFormula" -> DFinalStates $ parseWhole expr value
    _ -> error [i|unknown keyowrd #{keyword}|]
  Just (t, _) -> error [i|unknown type #{t}|]
  Nothing -> error "empty identifier"

expr :: Parser STermStr
expr = buildExpressionParser table term <?> "expression"
  where
    table =
      [ [Prefix $ Free . Not <$ char '!']
      , [Infix (Free .: And <$ char '&') AssocLeft]
      , [Infix (Free .: Or <$ char '|') AssocLeft]
      ]

identifier :: Parser T.Text
identifier = Parsec.takeWhile (\case '_' -> True; x -> isAlphaNum x)

term :: Parser STermStr
term =
  "(" *> expr <* ")"
    <|> (Free . State <$> ("s" *> identifier))
    <|> (Pure <$> ("f" *> identifier))
    <|> (Free LTrue <$ "True")
    <|> (Free LFalse <$ "False")
    <|> (Free . Var <$> ("a" *> identifier))
    <?> "expected a term"

orize :: [Definition] -> (STermStr, STermStr, HM.HashMap T.Text STermStr, HM.HashMap T.Text STermStr)
orize defs =
  ( foldr (Free .: Or) (Free LFalse) $ init `appEndo` []
  , foldr (Free .: Or) (Free LFalse) $ final `appEndo` []
  , HM.fromListWith (Free .: Or) $ formulae `appEndo` []
  , HM.fromListWith (Free .: Or) $ states `appEndo` []
  )
  where
    (init, final, states, formulae) = execWriter $
      for defs $ \case
        DFormula name dterm -> tell (mempty, mempty, mempty, Endo ((name, dterm) :))
        DState name dterm -> tell (mempty, mempty, Endo ((name, dterm) :), mempty)
        DInitialStates dterm -> tell (Endo (dterm :), mempty, mempty, mempty)
        DFinalStates dterm -> tell (mempty, Endo (dterm :), mempty, mempty)

class ShowT a where
  showT :: a -> T.Text

instance ShowT T.Text where
  showT = id

type FormatD d m =
  FormatD_ d m (FormatA d (Term [g|q|] [g|v|] [g|r|]) [g|r|]) [g|q|] [g|v|] [g|r|]
type FormatM m = StateT Int (WriterT (Endo [T.Text]) m)
type FormatA (d :: TypeDict) x r =
  FormatA1
    ( Name "recur" (MkN (RecK r x T.Text) (Inc (Inc [d|any|])))
        :+: End
    )
    r
type FormatA1 d' r =
  Name "isTree" (Mk IsTree [d'|recur|])
    :+: Name "rec" (Mk (MfnK r T.Text) [d'|recur|])
    :+: d'
type FormatD_ d (m :: * -> *) (d' :: TypeDict) (q :: *) (v :: *) (r :: *) =
  D.Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d' ~ FormatA d (Term q v r) r)
    :|: D.Name "" (RecRecur [d'|recur|] (FormatM m))
    :|: D.End
format ::
  forall d q v r m d'.
  (Monad m, D.ToConstraint (FormatD_ d m d' q v r), ShowT v, ShowT q) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  m T.Text
format init final (qCount, i2q, i2r, q2i) = do
  let qis = [0 .. qCount - 1]
  ((init', final', qs'), log) <- runWriterT $ flip evalStateT (0 :: Int) do
    convert <- recur @ [d'|recur|] \x -> do
      txt <- case x of
        LTrue -> return [i|kTrue|]
        LFalse -> return [i|kFalse|]
        State q -> return [i|s#{showT q}|]
        Var v -> return [i|a#{showT v}|]
        Not r -> do r' <- [d'|monadfn|rec|] r; return [i|!(#{r'})|]
        And a b -> do a' <- [d'|monadfn|rec|] a; b' <- [d'|monadfn|rec|] b; return [i|(#{a'}) & (#{b'})|]
        Or a b -> do a' <- [d'|monadfn|rec|] a; b' <- [d'|monadfn|rec|] b; return [i|(#{a'}) | (#{b'})|]
      [d'|ask|isTree|] >>= \case
        True -> return txt
        False -> do
          fIx :: Int <- lift get
          lift $ put $ fIx + 1
          lift $ lift $ tell $ Endo (txt :)
          return [i|f#{fIx}|]
    (,,) <$> convert init <*> convert final <*> mapM (convert . i2r) qis

  return $
    T.unlines $
      [i|@kInitialFormula: #{init'}|] :
      [i|@kFinalFormula: #{final'}|] :
      zipWith (\n t -> [i|@s#{showT $ i2q n}: #{t}|]) [0 ..] qs'
        ++ zipWith (\n t -> [i|@f#{n}: #{t}|]) [0 ..] (log `appEndo` [])

parseIORef ::
  forall s r r' d result.
  ( r ~ Afa.IORef.Ref (Term T.Text T.Text)
  , d ~ IORefRemoveFinalsD T.Text T.Text r r'
  ) =>
  T.Text ->
  IO (r, r, (Int, Int -> T.Text, Int -> r, T.Text -> Int))
parseIORef = Afa.Convert.PrettyStranger2.parse @d

formatIORef ::
  forall s r r' d result.
  ( r ~ Afa.IORef.Ref (Term T.Text T.Text)
  , d ~ IORefRemoveFinalsD T.Text T.Text r r'
  ) =>
  r ->
  r ->
  (Int, Int -> T.Text, Int -> r, T.Text -> Int) ->
  IO T.Text
formatIORef = Afa.Convert.PrettyStranger2.format @d
