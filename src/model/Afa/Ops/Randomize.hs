{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Afa.Ops.Randomize where

import Data.Array.Base (unsafeWrite)
import Data.Semigroup (First(..))
import Data.Array.ST
import Control.Monad.ST
import Data.Traversable
import System.Random
import Control.Monad.State.Strict
import qualified Data.HashSet as HS
import Data.Monoid (Endo(..))
import Control.Lens
import qualified Data.HashMap.Strict as HM
import Control.Monad.Random.Class
import Control.Monad.Random.Lazy
import System.Random.Shuffle
import Data.Array
import qualified Data.List.NonEmpty as NE
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons

import Afa.Lib.LiftArray
import Afa
import Afa.Bool
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

{-# INLINABLE randomizeIO #-}
randomizeIO :: BoolAfaUnswallowed Int -> IO (BoolAfaUnswallowed Int)
randomizeIO bafa = getStdRandom$ runRand$ randomize bafa

{-# INLINABLE randomize #-}
randomize :: MonadRandom m => BoolAfaUnswallowed Int -> m (BoolAfaUnswallowed Int)
randomize (BoolAfa bterms (Afa mterms states init)) = do
  let vars = (`appEndo` HS.empty)$
        foldMap (BTerm.appMTFol BTerm.mtfol0{ BTerm.mtfolP = Endo . HS.insert }) bterms
  shuffledVars <- shuffleM (HS.toList vars)
  let varPermut = HM.fromList$ zip shuffledVars [0..]
  btermPermut <- listArray (bounds bterms) <$> shuffleM (range$ bounds bterms)
  redirectedBTerms <- for bterms$
    BTerm.appMTra BTerm.mtra0
      { BTerm.mtraPredicate = return . BTerm.Predicate . (varPermut HM.!)
      , BTerm.mtraAnd = \xs ->
          BTerm.And . NE.fromList . map (btermPermut!) <$> shuffleM (NE.toList xs)
      , BTerm.mtraOr = \xs ->
          BTerm.Or . NE.fromList . map (btermPermut!) <$> shuffleM (NE.toList xs)
      , BTerm.mtraNot = return . BTerm.Not . (btermPermut !)
      }
  let
    shuffledBTerms = array (bounds bterms)$
      zip (elems btermPermut) (elems redirectedBTerms)
    (btermPermut', listArray (bounds bterms) -> bterms') = runST action where
      action :: forall s. ST s (Array Int Int, [BTerm.Term Int Int])
      action = runNoConsT$ do
        (gs :: LSTArray s Int (Maybe (First Int))) <- newArray (bounds bterms) Nothing
        fmap (listArray (bounds bterms))$
          for (range (bounds bterms))$ flip dfs gs$ \rec -> \case
            (Just (First j), _) -> return j
            (_, i) -> do
              bterm' <- BTerm.appMTTra BTerm.mttra0{BTerm.mttraT = rec . (Nothing,)}$
                shuffledBTerms!i
              j <- nocons bterm'
              unsafeWrite gs i$ Just$ First j
              return j

  statePermut <- listArray (bounds states) <$> shuffleM (range$ bounds states)
  mtermPermut <- listArray (bounds mterms) <$> shuffleM (range$ bounds mterms)
  redirectedMTerms <- for mterms$
    MTerm.appMTra MTerm.mtra0
      { MTerm.mtraState = return . MTerm.State . (statePermut !)
      , MTerm.mtraPredicate = return . MTerm.Predicate .
          (btermPermut'!) . (btermPermut!)
      , MTerm.mtraAnd = \xs ->
          MTerm.And . NE.fromList . map (mtermPermut!) <$> shuffleM (NE.toList xs)
      , MTerm.mtraOr = \xs ->
          MTerm.Or . NE.fromList . map (mtermPermut!) <$> shuffleM (NE.toList xs)
      }

  let
    shuffledMTerms = array (bounds mterms)$
      zip (elems mtermPermut) (elems redirectedMTerms)
    (mtermPermut', listArray (bounds mterms) -> mterms') = runST action where
      action :: forall s. ST s (Array Int Int, [MTerm.Term Int Int Int])
      action = runNoConsT$ do
        (gs :: LSTArray s Int (Maybe (First Int))) <- newArray (bounds mterms) Nothing
        fmap (listArray (bounds mterms))$
          for (range (bounds mterms))$ flip dfs gs$ \rec -> \case
            (Just (First j), _) -> return j
            (_, i) -> do
              mterm' <- MTerm.appMTTra MTerm.mttra0{MTerm.mttraT = rec . (Nothing,)}$
                shuffledMTerms!i
              j <- nocons mterm'
              unsafeWrite gs i$ Just$ First j
              return j

    redirectedStates = states <&> (mtermPermut'!) . (mtermPermut!)

  return BoolAfa
    { boolTerms = bterms'
    , afa = Afa
        { terms = mterms'
        , states = array (bounds states)$
            zip (elems statePermut) (elems redirectedStates)
        , initState = statePermut ! init
        }
    }
