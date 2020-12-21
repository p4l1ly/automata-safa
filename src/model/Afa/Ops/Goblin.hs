{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Afa.Ops.Goblin where

import Data.Functor
import Control.Monad
import Data.Array
import Control.Monad.ST
import Control.Lens
import Control.Monad.Trans
import Control.RecursionSchemes.Lens
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Void
import Data.Maybe

import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import Afa
import Afa.Term.Mix

split
  :: Term p q (Maybe tq, ta)
  -> Either (Term Void q tq, [ta]) (Term p tq ta)
split LTrue = Left (LTrue, [])
split (State q) = Left (State q, [])
split (Predicate p) = Right (Predicate p)
split (Or ts) = case sequence tqs of
  Just ts' -> Left (Or ts', [])
  _ -> Right$ Or tas
  where (tqs, tas) = NE.unzip ts
split (And ts) = case mapM fst ts of
  Just ts' -> Left (And ts', [])
  _ | null tqs -> Right$ And$ NE.map snd ts
    | otherwise -> Left (And$ NE.fromList tqs, tas)
  where
  (map (fromJust . fst) -> tqs, map snd -> tas) = NE.partition (isJust . fst) ts

split'
  :: (Show p, Monad m)
  => Term p Int (Maybe (Int, Bool), Int)
  -> NoConsT (Term Void Int (Int, Bool))
       (NoConsT (Term p (Int, Bool) Int) m)
       (Maybe (Int, Bool), Int)
split' x = case split x of
  Left (State ((, False) -> q), []) -> (Just q,) <$> lift (nocons$ State q)
  Left (State _, _) -> error "state with adep arguments"
  Left (tq, []) -> do
    q <- (, True) <$> nocons tq
    (Just q,) <$> lift (nocons$ State q)
  Left (tq, tas) -> do
    q <- (, True) <$> nocons tq
    a <- lift$ nocons$ State q
    (Just q,) <$> lift (nocons$ And$ a :| tas)
  Right ta -> (Nothing,) <$> lift (nocons ta)

isGate (Or _) = True
isGate (And _) = True
isGate _ = False

goblin :: forall p. Show p => AfaUnswallowed p -> Maybe (AfaUnswallowed p)
goblin afa@Afa{terms, states} = guard (any isGate qdep) $> afa
  { terms = listArray'$ adep' ++ qdep'
  , states = listArray'$ elems states' ++ zipWith const [adepL ..] qdep
  }
  where
  ((ixMap, qdep), adep) = runST action where
    action :: forall s. ST s
      ( (Array Int (Maybe (Int, Bool), Int)
        , [Term Void Int (Int, Bool)]
        )
      , [Term p (Int, Bool) Int]
      )
    action = runNoConsT$ runNoConsT$
      cataScanT' @(LLSTArray s) traversed split' terms

  stateL = rangeSize$ bounds states
  adepL = length adep
  adep' = adep <&> runIdentity . modChilds pureChildMod {lQ = shiftState}
  qdep' = qdep <&> runIdentity . modChilds pureChildMod {lP = absurd, lT = shiftQDep}

  shiftState (i, new) = Identity$ if new then i + stateL else i
  shiftQDep (i, new) = Identity$ if new then i + adepL else snd$ ixMap!(states!i)

  states' = fmap (snd . (ixMap!)) states
