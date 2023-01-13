{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
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
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Convert.PrettyStranger where

import Afa.Convert.Identifier
import Afa.Term (Term (..))
import Afa.IORef
import qualified Data.Text as T
import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import Control.Monad.Free
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
import Data.String.Interpolate.IsString (i)
import qualified Data.HashMap.Strict as HM
import qualified Data.Text.IO as TIO

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

-- type ParseD d m = ParseD_ d m (ParseA d [g|r|]) [g|r|]
-- type ParseA d r =
--   Name "shareTree" (Inherit (Explicit r r) [g|shareTree|])
--     :+: Name "buildTreeD" (Name "build" (Inherit (Explicit (Term T.Text T.Text r) r) [g|buildTree|]) :+: d)
--     :+: End
-- type ParseD_ (d :: TypeDict) (m :: * -> *) (d1 :: TypeDict) (r :: *) =
--   Name "aliases" (r ~ [g|r|], d1 ~ ParseA d r)
--     :+: Name "" (MonadFn [g1|shareTree|] m)
--     :+: Name "" (BuildD [g1|buildTreeD|] (Term T.Text T.Text) r m)
--     :+: End
-- parse ::
--   forall d m r d1.
--   ToConstraint (ParseD_ d m d1 r) =>
--   [AfaDefinition] ->
--   m (r, r, (Int, Int -> T.Text, Int -> r, T.Text -> Int))
-- parse defs = do
--   (initR, finalR, stateRs) <- flip evalStateT HM.empty $ do
--     (,,) <$> convert init <*> convert final <*> mapM convert states
--   let stateList = HM.toList stateRs
--       arr = listArray (0, HM.size stateRs - 1) stateList
--       stateNames = map fst stateList
--       state2ix = HM.fromList $ zip stateNames [0 ..]
--       states = (rangeSize $ bounds arr, fst . (arr !), snd . (arr !), (state2ix HM.!))
--   return (initR, finalR, states)
--   where
--     (init, final, formulae, states) = orize defs
--     convert :: Free (Term T.Text T.Text) T.Text -> StateT (HM.HashMap T.Text (Maybe r)) m r
--     convert f = mapM fRec f >>= buildFree @(LiftTags [g1|buildTreeD|])
--     fRec :: T.Text -> StateT (HM.HashMap T.Text (Maybe r)) m r
--     fRec name =
--       gets (HM.!? name) >>= \case
--         Just Nothing -> error $ "cycle " ++ T.unpack name
--         Just (Just r) -> return r
--         Nothing -> do
--           modify $ HM.insert name Nothing
--           (f :: Free (Term T.Text T.Text) r) <- mapM fRec (formulae HM.! name)
--           r <- buildFree @(LiftTags [g1|buildTreeD|]) f >>= monadfn @(Inc [g1|shareTree|])
--           modify $ HM.insert name (Just r)
--           return r

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

orize :: [AfaDefinition] -> (TxtTerm, TxtTerm, HM.HashMap T.Text TxtTerm, HM.HashMap T.Text TxtTerm)
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
data FormatFormulaA d x r

type instance Definition (FormatFormulaA d x r) =
  -- Name "recur" (MkN (RecK r x T.Text) [g|any|])
      Name "deref" (Inherit (Explicit r (Term [g|q|] [g|v|] [g|r|])) [g|deref|])
      :+: Name "refIsTree" (Inherit (Explicit r Bool) [g|isTree|])
      :+: Name "isTree" (Inherit (Explicit r Bool) (Get "recur" (Follow (FormatFormulaA d x r))))
      :+: Name "rec" (Inherit (Explicit r T.Text) (Get "recur" (Follow (FormatFormulaA d x r))))
      :+: Name "self" (Inherit (Explicit () r)  (Get "recur" (Follow (FormatFormulaA d x r))))
      :+: End

type FormatFormulaD_ d (m :: * -> *) d1 q v r =
  Name "aliases" (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|], d1 ~ FormatFormulaA d (Term q v r) r)
    :+: Name "show" (Identify v, Identify q)
    -- :+: Name "rec" (RecRecur [g1|recur|] m)
    :+: Name "deref" (MonadFn [g1|deref|] m)
    :+: Name "refIsTree" (MonadFn [g1|isTree|] m)
    :+: End
formatFormula ::
  forall d q v r d1.
  ToConstraint (FormatFormulaD_ d IO d1 q v r) =>
  IO (r -> IO T.Text, IO [(Int, T.Text)])
formatFormula = do
  let rec = monadfn @[g1|rec|]
  vFIx <- newIORef (0 :: Int)
  stack <- newIORef ([] :: [(Int, T.Text)])
  let algebra x = do
        monadfn @[g1|isTree|] () >>= \case
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
              State q -> return $ T.cons 's' (identify q)
              Var v -> return $ T.cons 'a' (identify v)
              Not !r -> do
                !r' <- rec r
                monadfn @(Inc [g1|refIsTree|]) r >>= \case
                  True ->
                    monadfn @(Inc [g1|deref|]) r <&> \case
                      And _ _ -> T.concat ["!(", r', ")"]
                      Or _ _ -> T.concat ["!(", r', ")"]
                      _ -> T.cons '!' r'
                  False -> return $ T.cons '!' r'
              And !a !b -> do
                !a' <- rec a
                !b' <- rec b
                a'' <-
                  monadfn @(Inc [g1|refIsTree|]) a >>= \case
                    True -> do
                      monadfn @(Inc [g1|deref|]) a <&> \case
                        Or _ _ -> T.concat ["(", a', ")"]
                        _ -> a'
                    False -> return a'
                b'' <-
                  monadfn @(Inc [g1|refIsTree|]) b >>= \case
                    True ->
                      monadfn @(Inc [g1|deref|]) b <&> \case
                        Or _ _ -> T.concat ["(", b', ")"]
                        _ -> b'
                    False -> return b'
                return $ T.concat [a'', " & ", b'']
              Or !a !b -> do
                !a' <- rec a
                !b' <- rec b
                at <- monadfn @(Inc [g1|deref|]) a
                bt <- monadfn @(Inc [g1|deref|]) b
                a'' <-
                  monadfn @(Inc [g1|refIsTree|]) a >>= \case
                    True -> do
                      monadfn @(Inc [g1|deref|]) a <&> \case
                        And _ _ -> T.concat ["(", a', ")"]
                        _ -> a'
                    False -> return a'
                b'' <-
                  monadfn @(Inc [g1|refIsTree|]) b >>= \case
                    True ->
                      monadfn @(Inc [g1|deref|]) b <&> \case
                        And _ _ -> T.concat ["(", b', ")"]
                        _ -> b'
                    False -> return b'
                return $ T.concat [a'', " | ", b'']

  convert <- recur @[g1|recur|] algebra
  return (convert, readIORef stack)

format ::
  forall d q v r d1.
  ToConstraint (FormatFormulaD d IO) =>
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
    TIO.putStr (identify $ i2q i)
    TIO.putStr ": "
    TIO.putStrLn =<< convert (i2r i)

  getShared >>= mapM_ \(i, txt) -> do
    TIO.putStr "@f"
    putStr (show i)
    TIO.putStr ": "
    TIO.putStrLn txt
