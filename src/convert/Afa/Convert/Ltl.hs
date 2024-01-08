{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Afa.Convert.Ltl where

import Data.List
import Control.Monad
import Data.Char
import Data.Composition ((.:))
import Data.Either
import Data.Fix
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
import qualified Data.Text as T
import Data.Hashable
import GHC.Generics hiding ((:+:))
import Generic.Data (Generically1 (..))
import Data.Functor.Classes
import Control.Applicative
import System.IO.Unsafe
import System.Random
import qualified Afa.IORef as AIO
import InversionOfControl.TypeDict
import Afa.Build
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import qualified Data.HashSet as HS
import qualified Afa.Term as Afa
import qualified Afa.States as Afa
import Data.IORef
import qualified InversionOfControl.Recur as R
import Control.Monad.Trans
import Control.Monad.Free
import Afa.ShallowHashable

data Ltl rec
  = Var !Int
  | LTrue
  | LFalse
  | And ![rec]
  | Or ![rec]
  | Not !rec
  | Next !rec
  | Until !rec !rec
  | WeakUntil !rec !rec
  | Globally !rec
  | Finally !rec
  | Release !rec !rec
  | StrongRelease !rec !rec
  deriving (Functor, Foldable, Traversable, Show, Generic, Generic1)
  deriving (Show1) via (Generically1 Ltl)

instance ShallowEq rec => Eq (Ltl rec) where
  LTrue == LTrue = True
  LFalse == LFalse = True
  Var v1 == Var v2 = v1 == v2
  And rs1 == And rs2 = and $ zipWith shallowEq rs1 rs2
  Or rs1 == Or rs2 = and $ zipWith shallowEq rs1 rs2
  Not r1 == Not r2 = r1 `shallowEq` r2
  Next r1 == Next r2 = r1 `shallowEq` r2
  Globally r1 == Globally r2 = r1 `shallowEq` r2
  Finally r1 == Finally r2 = r1 `shallowEq` r2
  Until r11 r12 == Until r21 r22 = r11 `shallowEq` r21 && r12 `shallowEq` r22
  WeakUntil r11 r12 == WeakUntil r21 r22 = r11 `shallowEq` r21 && r12 `shallowEq` r22
  Release r11 r12 == Release r21 r22 = r11 `shallowEq` r21 && r12 `shallowEq` r22
  StrongRelease r11 r12 == StrongRelease r21 r22 = r11 `shallowEq` r21 && r12 `shallowEq` r22
  _ == _ = False

instance ShallowHashable r => Hashable (Ltl r) where
  hashWithSalt salt LTrue = hashWithSalt' salt 143080932
  hashWithSalt salt LFalse = hashWithSalt' salt 3211304
  hashWithSalt salt (Var q) = hashWithSalt (hashWithSalt' salt 398201981) q
  hashWithSalt salt (And rs) = foldl' shallowHash (hashWithSalt' salt 83271) rs
  hashWithSalt salt (Or rs) = foldl' shallowHash (hashWithSalt' salt 483178) rs
  hashWithSalt salt (Not r) = shallowHash (hashWithSalt' salt 73274521) r
  hashWithSalt salt (Next r) = shallowHash (hashWithSalt' salt 8584371) r
  hashWithSalt salt (Finally r) = shallowHash (hashWithSalt' salt 431513278) r
  hashWithSalt salt (Globally r) = shallowHash (hashWithSalt' salt 92437) r
  hashWithSalt salt (Until r1 r2) = shallowHash (shallowHash (hashWithSalt' salt 4324142) r1) r2
  hashWithSalt salt (WeakUntil r1 r2) = shallowHash (shallowHash (hashWithSalt' salt 47193) r1) r2
  hashWithSalt salt (Release r1 r2) = shallowHash (shallowHash (hashWithSalt' salt 938563) r1) r2
  hashWithSalt salt (StrongRelease r1 r2) = shallowHash (shallowHash (hashWithSalt' salt 37258433) r1) r2

instance ShallowEq (Fix f) where
  shallowEq _ _ = False

instance ShallowHashable (Fix f) where
  shallowHash _ _ = unsafePerformIO randomIO

data EmptyO
type instance Definition EmptyO = End

type LtlRef = AIO.Ref Ltl
type LtlTerm = Ltl LtlRef
type LtlBuild = 'K Zero (Explicit LtlTerm LtlRef AIO.Build)
type LtlIsTree = 'K Zero (Explicit LtlRef Bool AIO.IsTree)
type RCata = R.Explicit ('K Zero AIO.RCata) Zero LtlRef (LtlRef, LtlTerm)

type AfaRef = AIO.Ref (Afa.MultiwayTerm Int Int)
type AfaTerm = Afa.MultiwayTerm Int Int AfaRef
type AfaBuild = 'K Zero (Explicit AfaTerm AfaRef AIO.Build)
type AfaShare = 'K Zero (Explicit AfaRef AfaRef AIO.Share)

data AfaO
type instance Definition AfaO = 
  Name "qs" (Afa.StateList Int AfaRef)
    :+: Name "term" AfaTerm
    :+: Follow (AIO.IORefO EmptyO)

parseWhole :: Parser a -> T.Text -> a
parseWhole parser str = case Parsec.parse parser str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p (T.pack "") of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseLtl :: T.Text -> Fix Ltl
parseLtl = parseWhole term . T.filter (not . isSpace)

operator :: Parser (Fix Ltl)
operator =
  (canonicalize LTrue LFalse And <$> (char '&' *> many1 term))
    <|> (canonicalize LFalse LTrue Or <$> (char '|' *> many1 term))
    <|> (Fix . Not <$> (char '!' *> term))
    <|> (Fix . Next <$> (char 'X' *> term))
    <|> (Fix . Globally <$> (char 'G' *> term))
    <|> (Fix . Finally <$> (char 'F' *> term))
    <|> (Fix .: Until <$> (char 'U' *> term) <*> term)
    <|> (Fix .: Release <$> (char 'R' *> term) <*> term)
    <|> (Fix .: WeakUntil <$> (char 'W' *> term) <*> term)
    <|> (Fix .: StrongRelease <$> (char 'M' *> term) <*> term)

canonicalize ::
  Ltl (Fix Ltl) -> Ltl (Fix Ltl) -> ([Fix Ltl] -> Ltl (Fix Ltl)) -> [Fix Ltl] -> Fix Ltl
canonicalize ignore force make ltls
  | force `HS.member` ltls' = Fix force
  | otherwise = case map Fix $ HS.toList $ HS.delete ignore ltls' of
      [] -> Fix ignore
      [x] -> x
      xs -> Fix $ make xs
  where ltls' = HS.fromList $ map unFix ltls

term :: Parser (Fix Ltl)
term =
  "(" *> operator <* ")"
    <|> (Fix . Var . read <$> (char 'a' *> many1 digit))
    <|> (Fix LTrue <$ char 't')
    <|> (Fix LFalse <$ char 'f')

preprocess :: Fix Ltl -> IO LtlRef
preprocess ltl = do
  ltl1 <- buildFix @LtlBuild $ pushNeg True ltl
  sharingDetector <- AIO.getSharingDetector
  ltl2 <- sharingDetector ltl1
  (countUpR, finalize) <- AIO.getUnsharingDetector
    (\case Var _ -> False; LTrue -> False; LFalse -> False; _shareables -> True)
  countUpR ltl2
  finalizeR <- finalize
  finalizeR ltl2

-- deRelease :: Fix Ltl -> Fix Ltl
-- deRelease (Fix (Release x y)) = Fix $ WeakUntil y (Fix $ And [x, y])
-- deRelease (Fix (StrongRelease x y)) = Fix $ Until y (Fix $ And [x, y])
-- deRelease (Fix fr) = Fix $ fmap deRelease fr

pushNeg :: Bool -> Fix Ltl -> Fix Ltl
pushNeg False (Fix (And ts)) = Fix $ Or $ map (pushNeg False) ts
pushNeg False (Fix (Or ts)) = Fix $ And $ map (pushNeg False) ts
pushNeg False (Fix LTrue) = Fix LFalse
pushNeg False (Fix LFalse) = Fix LTrue
pushNeg False (Fix (Var v)) = Fix $ Not $ Fix $ Var v
pushNeg False (Fix (Globally t)) = Fix $ Finally $ pushNeg False t
pushNeg False (Fix (Finally t)) = Fix $ Globally $ pushNeg False t
pushNeg False (Fix (Release x y)) = Fix $ Until (pushNeg False x) (pushNeg False y)
pushNeg False (Fix (Until x y)) = Fix $ Release (pushNeg False x) (pushNeg False y)
pushNeg False (Fix (StrongRelease x y)) = Fix $ WeakUntil (pushNeg False x) (pushNeg False y)
pushNeg False (Fix (WeakUntil x y)) = Fix $ StrongRelease (pushNeg False x) (pushNeg False y)
pushNeg b (Fix (Not t)) = pushNeg (not b) t
pushNeg b (Fix fr) = Fix $ fmap (pushNeg b) fr

data BuildShareSharedO
type instance Definition BuildShareSharedO =
  Name "fr'" AfaTerm
    :+: Name "r'" AfaRef
    :+: Name "r" LtlRef
    :+: Follow (AIO.IORefO EmptyO)

toAfa :: LtlRef -> IO (AfaRef, AfaRef, Afa.StateList Int AfaRef)
toAfa ltl = do
  statesRef <- newIORef []
  nonfinalsRef <- newIORef []
  stateCountRef <- newIORef 0

  let newState isFinal fn = do
        qix <- readIORef stateCountRef
        writeIORef stateCountRef (qix + 1)
        (trans, result) <- fn qix
        modifyIORef' statesRef ((qix, trans) :)
        unless isFinal do 
          modifyIORef' nonfinalsRef (qix :)
        return result

  init <- R.runRecur @RCata
    ( \recur (r0, fr0) ->
        let buildSh = buildShareShared @BuildShareSharedO r0
        in mapM recur fr0 >>= lift . \case
          LTrue -> buildSh Afa.LTrueMulti
          LFalse -> buildSh Afa.LFalseMulti
          Var q -> buildSh $ Afa.VarMulti q
          And xs -> buildSh $ Afa.AndMulti xs
          Or xs -> buildSh $ Afa.OrMulti xs
          Not x -> buildSh $ Afa.NotMulti x  -- Assumption: pushNeg has been applied.
          Next x -> newState False $ \qix -> (x,) <$> buildSh (Afa.StateMulti qix)
          Until x y -> newState False $ \qix -> do
            andNode <- buildFree @AfaBuild $ Free $ Afa.AndMulti [Free $ Afa.StateMulti qix, Pure x]
            orNode <- buildSh $ Afa.OrMulti [y, andNode]
            return (orNode, orNode)
          StrongRelease x y -> newState False $ \qix -> do
            orNode <- buildFree @AfaBuild $ Free $ Afa.OrMulti [Free $ Afa.StateMulti qix, Pure x]
            andNode <- buildSh $ Afa.AndMulti [y, orNode]
            return (andNode, andNode)
          WeakUntil x y -> do
            newState True $ \qix -> do
              qNode <- monadfn @AfaBuild $ Afa.StateMulti qix
              andNode <- monadfn @AfaBuild $ Afa.AndMulti [qNode, x]
              orNode <- monadfn @AfaBuild $ Afa.OrMulti [y, andNode]
              result <- buildSh $ Afa.OrMulti [qNode, y]
              return (orNode, result)
          Release x y -> do
            newState True $ \qix -> do
              qNode <- monadfn @AfaBuild $ Afa.StateMulti qix
              orNode <- monadfn @AfaBuild $ Afa.OrMulti [qNode, x]
              andNode <- monadfn @AfaBuild $ Afa.AndMulti [y, orNode]
              result <- buildSh $ Afa.OrMulti [qNode, andNode]
              return (andNode, result)
          Globally x -> do
            newState True $ \qix -> do
              qNode <- buildSh $ Afa.StateMulti qix
              andNode <- monadfn @AfaBuild $ Afa.AndMulti [qNode, x]
              return (andNode, qNode)
          Finally x -> do
            newState False $ \qix -> do
              qNode <- monadfn @AfaBuild $ Afa.StateMulti qix
              orNode <- buildSh $ Afa.OrMulti [qNode, x]
              return (orNode, orNode)
    )
    ($ ltl)

  states <- readIORef statesRef
  nonfinals <- readIORef nonfinalsRef
  final <-
    if null nonfinals
      then monadfn @AfaBuild Afa.LTrueMulti
      else
        buildFix @AfaBuild $ Fix $ Afa.AndMulti $
          map (Fix . Afa.NotMulti . Fix . Afa.StateMulti) nonfinals

  return (init, final, Afa.StateList states)

textToAfa :: T.Text -> IO (AfaRef, AfaRef, Afa.StateList Int AfaRef)
textToAfa txt = toAfa =<< preprocess (parseLtl txt)
