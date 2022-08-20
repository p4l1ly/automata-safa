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

module Afa.Convert.PrettyStranger2 where

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
import Control.Monad.Writer.Strict
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
  D.ToConstraint (ParseD_ d m d' r) =>
  [Definition] ->
  m (r, r, (Int, Int -> T.Text, Int -> r, T.Text -> Int))
parse defs = do
  (initR, finalR, stateRs) <- flip evalStateT HM.empty $ do
    (,,) <$> convert init <*> convert final <*> mapM convert states
  let stateList = HM.toList stateRs
      arr = listArray (0, HM.size stateRs - 1) stateList
      stateNames = map fst stateList
      state2ix = HM.fromList $ zip stateNames [0 ..]
      states = (rangeSize $ bounds arr, fst . (arr !), snd . (arr !), (state2ix HM.!))
  return (initR, finalR, states)
  where
    (init, final, formulae, states) = orize defs
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
          r <- buildFree @(LiftTags [g'|buildTreeD|]) f >>= monadfn @(Inc [d'|shareTree|])
          modify $ HM.insert name (Just r)
          return r

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
    _ -> error [i|unknown keyword #{keyword}|]
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
    <|> (Free LTrue <$ "kTrue")
    <|> (Free LFalse <$ "kFalse")
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
            return $ do T.cons 'f' (T.pack (show fIx))
        where
          contents =
            case x of
              LTrue -> return "kTrue"
              LFalse -> return "kFalse"
              State q -> return $ T.cons 's' (showT q)
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

  convert <- recur @ [d'|recur|] algebra
  return (convert, readIORef stack)

format ::
  forall d q v r d'.
  D.ToConstraint (FormatFormulaD d IO) =>
  [g|r|] ->
  [g|r|] ->
  (Int, Int -> [g|q|], Int -> [g|r|], [g|q|] -> Int) ->
  IO ()
format init final (qCount, i2q, i2r, q2i) = do
  (convert, getShared) <- formatFormula @d

  TIO.putStr "@kInitialFormula: "
  TIO.putStrLn =<< convert init
  TIO.putStr "@kFinalFormula: "
  TIO.putStrLn =<< convert final
  for_ [0 .. qCount - 1] \i -> do
    TIO.putStr "@s"
    TIO.putStr (showT $ i2q i)
    TIO.putStr ": "
    TIO.putStrLn =<< convert (i2r i)

  getShared >>= mapM_ \(i, txt) -> do
    TIO.putStr "@f"
    putStr (show i)
    TIO.putStr ": "
    TIO.putStrLn txt

parseIORef ::
  forall r r' d result.
  ( r ~ Afa.IORef.Ref (Term T.Text T.Text)
  , d ~ IORefRemoveFinalsD T.Text T.Text r r'
  ) =>
  [Definition] ->
  IO (r, r, (Int, Int -> T.Text, Int -> r, T.Text -> Int))
parseIORef = Afa.Convert.PrettyStranger2.parse @d

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
formatIORef = Afa.Convert.PrettyStranger2.format @d

class ShowT a where
  showT :: a -> T.Text

instance ShowT T.Text where
  showT = id

instance ShowT Word32 where
  showT = T.pack . show

instance ShowT Word8 where
  showT = T.pack . show

instance ShowT AfaC.Range16 where
  showT (AfaC.Range16 a b) = [i|R#{a}_#{b}|]

instance ShowT q => ShowT (SyncQs q) where
  showT (QState q) = [i|Q#{showT q}|]
  showT SyncState = "Sync"

instance (ShowT q, ShowT v) => ShowT (SyncVar q v) where
  showT (VVar v) = [i|V#{showT v}|]
  showT (QVar v) = [i|Q#{showT v}|]
  showT FVar = "F"

formatRange16Nfa :: AfaC.Range16Nfa -> IO ()
formatRange16Nfa (AfaC.Range16Nfa states initial finals) = do
  TIO.putStrLn [i|@kInitialFormula: s#{initial}|]
  let nonfinals =
        accumArray (\_ _ -> False) True (0, fromIntegral (V.length states - 1)) $
          map (,()) $ toList finals
  let nonfinals' = filter (nonfinals !) (range $ bounds nonfinals)
  let finals'
        | V.length states == 0 = "kTrue"
        | otherwise = T.intercalate " & " $ nonfinals' <&> \q -> [i|!s#{q}|]
  TIO.putStrLn [i|@kFinalFormula: #{finals'}|]
  states & itraverse \qi ts ->
    for ts \(AfaC.ConjunctR16Q ranges qi') -> do
      let ranges' =
            T.intercalate " | " . toList $
              ranges <&> \(AfaC.Range16 a b) -> [i|[#{a};#{b}]|]
      TIO.putStrLn [i|@q#{qi}: (#{ranges'}) & s#{qi'}|]
  return ()

instance ShowT q => ShowT (Qombo q) where
  showT (Qombo n q) = [i|C#{n}_#{showT q}|]
