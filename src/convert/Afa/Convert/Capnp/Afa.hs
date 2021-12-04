{-# LANGUAGE ScopedTypeVariables #-}

module Afa.Convert.Capnp.Afa where

import qualified Capnp
import qualified Capnp.Gen.Afa.Model.Succinct.Pure as AfaC
import qualified Capnp.Gen.Afa.Model.Term.Pure as TermC
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Control.Lens
import Data.Array
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.List.NonEmpty as NE
import Data.Monoid (Endo (..))
import Data.Semigroup (Max (..))
import System.IO

import Afa
import Afa.Bool
import Afa.Lib (listArray')
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

hReadAfa :: Handle -> IO (BoolAfaUnswallowed Int)
hReadAfa h = deserializeAfa <$> Capnp.hGetValue h maxBound

hWriteAfa :: Bool -> BoolAfaUnswallowed Int -> Handle -> IO ()
hWriteAfa collapseVars afa h = Capnp.hPutValue h $ serializeAfa collapseVars afa

deserializeAfa :: AfaC.BoolAfa -> BoolAfaUnswallowed Int
deserializeAfa (AfaC.BoolAfa aterms mterms states _) =
  BoolAfa
    (listArray' $ map deserializeBTerm $ V.toList aterms)
    ( Afa
        (listArray' $ map deserializeMTerm $ V.toList mterms)
        (listArray' $ map fromIntegral $ V.toList states)
        0
    )

deserializeBTerm :: TermC.BoolTerm11 -> BTerm.Term Int Int
deserializeBTerm TermC.BoolTerm11'litTrue = BTerm.LTrue
deserializeBTerm TermC.BoolTerm11'litFalse = BTerm.LFalse
deserializeBTerm (TermC.BoolTerm11'predicate p) = BTerm.Predicate $ fromIntegral p
deserializeBTerm (TermC.BoolTerm11'not x) = BTerm.Not $ fromIntegral x
deserializeBTerm (TermC.BoolTerm11'or xs) = BTerm.Or $ iVecToNe xs
deserializeBTerm (TermC.BoolTerm11'and xs) = BTerm.And $ iVecToNe xs

deserializeMTerm :: TermC.PredicateQTerm111 -> MTerm.Term Int Int Int
deserializeMTerm TermC.PredicateQTerm111'litTrue = MTerm.LTrue
deserializeMTerm (TermC.PredicateQTerm111'predicate p) = MTerm.Predicate $ fromIntegral p
deserializeMTerm (TermC.PredicateQTerm111'state q) = MTerm.State $ fromIntegral q
deserializeMTerm (TermC.PredicateQTerm111'or xs) = MTerm.Or $ iVecToNe xs
deserializeMTerm (TermC.PredicateQTerm111'and xs) = MTerm.And $ iVecToNe xs

serializeAfa :: Bool -> BoolAfaUnswallowed Int -> AfaC.BoolAfa
serializeAfa collapseVars (BoolAfa bterms (Afa mterms states 0)) =
  AfaC.BoolAfa
    { AfaC.aterms = V.fromList $ map serializeBTerm $ elems bterms'
    , AfaC.mterms = V.fromList $ map serializeMTerm $ elems mterms
    , AfaC.states = V.fromList $ map fromIntegral $ elems states
    , AfaC.varCount = fromIntegral varCnt
    }
  where
    (varCnt, bterms') = if collapseVars then varCount bterms else varCount0 bterms

varCount :: (Traversable f) => f (BTerm.Term Int t) -> (Int, f (BTerm.Term Int t))
varCount arr = (count, arr')
  where
    vars =
      (`appEndo` HS.empty) $
        foldMap (BTerm.appMTFol BTerm.mtfol0{BTerm.mtfolP = Endo . HS.insert}) arr
    count = HS.size vars
    varMap = HM.fromList $ zip (HS.toList vars) [0 ..]
    arr' = arr <&> BTerm.appMTFun BTerm.mtfun0{BTerm.mtfunP = (varMap HM.!)}

varCount0 :: (Traversable f) => f (BTerm.Term Int t) -> (Int, f (BTerm.Term Int t))
varCount0 arr = (count + 1, arr)
  where
    count = getMax $ foldMap (BTerm.appMTFol BTerm.mtfol0{BTerm.mtfolP = Max}) arr

serializeBTerm :: BTerm.Term Int Int -> TermC.BoolTerm11
serializeBTerm BTerm.LTrue = TermC.BoolTerm11'litTrue
serializeBTerm BTerm.LFalse = TermC.BoolTerm11'litFalse
serializeBTerm (BTerm.Predicate p) = TermC.BoolTerm11'predicate $ fromIntegral p
serializeBTerm (BTerm.Not x) = TermC.BoolTerm11'not $ fromIntegral x
serializeBTerm (BTerm.Or xs) = TermC.BoolTerm11'or $ iNeToVec xs
serializeBTerm (BTerm.And xs) = TermC.BoolTerm11'and $ iNeToVec xs

serializeMTerm :: MTerm.Term Int Int Int -> TermC.PredicateQTerm111
serializeMTerm MTerm.LTrue = TermC.PredicateQTerm111'litTrue
serializeMTerm (MTerm.Predicate p) = TermC.PredicateQTerm111'predicate $ fromIntegral p
serializeMTerm (MTerm.State q) = TermC.PredicateQTerm111'state $ fromIntegral q
serializeMTerm (MTerm.Or xs) = TermC.PredicateQTerm111'or $ iNeToVec xs
serializeMTerm (MTerm.And xs) = TermC.PredicateQTerm111'and $ iNeToVec xs

iNeToVec = V.fromList . map fromIntegral . NE.toList
iVecToNe = NE.fromList . map fromIntegral . V.toList
