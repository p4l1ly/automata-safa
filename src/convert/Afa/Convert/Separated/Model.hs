{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Convert.Separated.Model where

import Control.Monad.Trans
import qualified Data.List.NonEmpty as NE
import Data.Traversable
import Data.Fix
import Data.Functor.Compose
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons
import Control.RecursionSchemes.Utils.HashCons
import Data.Array.ST
import Control.Monad.ST
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
import Data.Bifunctor
import Control.Lens
import Data.Either
import Data.List
import Data.Maybe
import Data.Monoid (Any(..), Endo(..))
import Data.Void
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Bool.Simplify as BTerm
import qualified Afa.Term.Mix.Simplify as MTerm
import Data.Array
import Data.Hashable
import qualified Afa as A

import Afa.Lib (listArray', DumbCount(Many))
import Afa.Lib.LiftArray

data Afa p = Afa
  { aterms :: Array Int (BTerm.Term p Int)
  , qterms :: Array Int (MTerm.Term Void Int Int)
  , states :: Array Int [(Maybe Int, Maybe Int)]
  , initState :: Int
  }
  deriving (Eq, Show)

reorderStates' :: Afa p -> Afa p
reorderStates' afa@Afa{qterms, states, initState} =
  afa{qterms = qterms', states = states', initState = initState'}
  where
  A.Afa qterms' states' initState' = A.reorderStates (A.Afa qterms states initState)

simplify :: forall p. (Eq p, Hashable p) => Afa p -> Either Bool (Afa p)
simplify afa@Afa{aterms, qterms, states, initState} = do
  (qterms2, states2, init2) <- simplifyStatesAndQTerms qIxMap qterms' states' initState
  let states2' = fmap absorb states2

  let Identity ((states3, qtermsFromStates), atermsFromStates) =
        runNoConsTFrom (rangeSize$ bounds aterms')$
        runNoConsTFrom (rangeSize$ bounds qterms2)$ do
          for states2'$ \ts -> let (pts, qts) = unzip ts in case ts of
            [_] -> return ts
            _ | all isNothing pts -> do
                  qt <- nocons$ MTerm.Or$ NE.fromList$ map fromJust qts
                  return [(Nothing, Just qt)]
              | all isNothing qts -> do
                  pt <- lift$ nocons$ BTerm.Or$ NE.fromList$ map fromJust pts
                  return [(Just pt, Nothing)]
              | otherwise -> return ts

  if sum (fmap length states3) == sum (fmap length states)
  then Right$ Afa aterms' qterms2 states2' init2
  else simplify Afa
    { aterms = listArray'$ elems aterms' ++ atermsFromStates
    , qterms = listArray'$ elems qterms2 ++ qtermsFromStates
    , states = states3
    , initState = init2
    }
  where
  (arefs, qrefs) = unzip$ concat$ elems states

  makeGs terms =
    accumArray (\_ x -> x) mempty (bounds terms) . map (, Any True) . catMaybes
  makeInitIxMap terms = listArray (bounds terms)$ map Right [0..]

  ags = makeGs aterms arefs
  qgs = makeGs qterms qrefs

  aInitIxMap = makeInitIxMap aterms
  qInitIxMap = makeInitIxMap qterms

  (aIxMap, aterms') = BTerm.simplifyDagUntilFixpoint ags (aInitIxMap, aterms)
  (qIxMap, qterms') = MTerm.simplifyDagUntilFixpoint qgs (qInitIxMap, qterms)

  states' = states <&> mapped . _1 %~ nothingToTrue . fmap (aIxMap!)

absorb :: [(Maybe Int, Maybe Int)] -> [(Maybe Int, Maybe Int)]
absorb ts = flip filter ts$ \case
  (Just a, Just q) | HS.member a singlesA || HS.member q singlesQ -> False
  _ -> True
  where
  singlesA = HS.fromList [a | (Just a, Nothing) <- ts]
  singlesQ = HS.fromList [q | (Nothing, Just q) <- ts]

nothingToTrue :: Maybe (Either Bool a) -> Either Bool a
nothingToTrue Nothing = Left True
nothingToTrue (Just x) = x

nothingToTrue' :: Maybe a -> Either Bool a
nothingToTrue' Nothing = Left True
nothingToTrue' (Just x) = Right x

leftToNothing :: Either Bool a -> Maybe a
leftToNothing (Right x) = Just x
leftToNothing _ = Nothing

emptyToFalse :: [a] -> Either Bool [a]
emptyToFalse [] = Left False
emptyToFalse xs = Right xs

simplifyStatesAndQTerms :: forall p. (Eq p, Hashable p)
  => Array Int (Either Bool Int)
  -> Array Int (MTerm.Term p Int Int)
  -> Array Int [(Either Bool Int, Maybe Int)]
  -> Int
  -> Either Bool
       ( Array Int (MTerm.Term p Int Int)
       , Array Int [(Maybe Int, Maybe Int)]
       , Int
       )
simplifyStatesAndQTerms ixMap mterms states init
  | rangeSize (bounds states2) == rangeSize (bounds states) =
      Right (mterms2, states2, init2)
  | otherwise = qMap!init >> simplifyStatesAndQTerms ixMap2 mterms2 states3 init2
  where
  states1 = states <&> mapped . _2 %~ nothingToTrue . fmap (ixMap!)

  getQs = (`appEndo` []) . MTerm.appMTFol MTerm.mtfol0{ MTerm.mtfolQ = Endo . (:) }
  parented = accumArray (\_ _ -> True) False (bounds states)$
    (init, ()) : map (, ()) (concatMap getQs$ elems mterms)
  (lefts, rights) = partition (isLeft . snd)$ zipWith partFn [0..] (elems states1)

  partFn i x = if parented!i then (i, partFn0 x) else (i, Left False)
  partFn0 xs = traverse partFnSingle xs >>= emptyToFalse . catMaybes
  partFnSingle (Left True, Left True) = Left True
  partFnSingle (Left False, _) = Right Nothing
  partFnSingle (_, Left False) = Right Nothing
  partFnSingle (a, b) = Right$ Just (leftToNothing a, leftToNothing b)

  lefts' = lefts <&> \case (i, Left x) -> (i, x)
  rights' = rights <&> \case (i, Right x) -> (HS.fromList x, [i])

  groups = HM.toList$ HM.fromListWith (++) rights'
  states2 = listArray'$ map (HS.toList . fst) groups
  states3 = states2 <&> mapped . _1 %~ nothingToTrue'
  oldToNew = concat$ zipWith (\i' (_, is) -> map (, i') is) [0..] groups

  qMap :: Array Int (Either Bool Int)
  qMap = array (bounds states)$ map (second Left) lefts' ++ map (second Right) oldToNew

  init2 = qMap!init & \case Right x -> x

  (ixMap2, listArray' -> mterms2) = runST action where
    action :: forall s. ST s (Array Int (Either Bool Int), [MTerm.Term p Int Int])
    action = runHashConsT$
      fmap (fmap fst) <$> cataScanT' @(LiftArray (STArray s)) traversed alg mterms

  alg t = case MTerm.modChilds MTerm.pureChildMod{ MTerm.lQ = (qMap!) } t of
    Left b -> return$ Left b
    Right t -> case MTerm.simplify ((Many,) . getCompose . unFix . snd) fst t of  -- no flattening, I'm lazy. not sure if it would change something...
      Left b -> return$ Left b
      Right (Left it) -> return$ Right it
      Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)
