{-# LANGUAGE DisambiguateRecordFields #-}

module Afa.Convert.Capnp.Separated where

import Afa.Convert.Capnp.Afa (deserializeBTerm, iNeToVec, iVecToNe, serializeBTerm, varCount)
import Afa.Convert.Separated.Model (Afa (..))
import Afa.Lib (listArray')
import qualified Afa.Term.Mix as MTerm
import qualified Capnp
import qualified Capnp.Gen.Afa.Model.Separated.Pure as AfaC
import qualified Capnp.Gen.Afa.Model.Term.Pure as TermC
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Control.Arrow
import Data.Array
import Data.Functor
import Data.Void
import System.IO

hWrite :: Afa Int -> Handle -> IO ()
hWrite afa h = Capnp.hPutValue h $ serializeAfa afa

serializeAfa :: Afa Int -> AfaC.BoolAfa
serializeAfa (Afa aterms qterms states 0) =
  AfaC.BoolAfa
    { AfaC.aterms = V.fromList $ map serializeBTerm $ elems aterms'
    , AfaC.varCount = fromIntegral varCnt
    , AfaC.qterms = V.fromList $ map serializeQTerm $ elems qterms
    , AfaC.states =
        V.fromList $
          elems states
            <&> V.fromList . map (uncurry AfaC.Conjunct11 . (toMaybe1 *** toMaybe1))
    }
  where
    (varCnt, aterms') = varCount aterms
serializeAfa _ = error "Separated.serializeAfa: only initState=0 is supported, please reorder states"

toMaybe1 :: Maybe Int -> AfaC.Maybe1
toMaybe1 Nothing = AfaC.Maybe1'nothing
toMaybe1 (Just a) = AfaC.Maybe1'just $ fromIntegral a

serializeQTerm :: MTerm.Term Void Int Int -> TermC.QTerm11
serializeQTerm MTerm.LTrue = TermC.QTerm11'litTrue
serializeQTerm (MTerm.State q) = TermC.QTerm11'state $ fromIntegral q
serializeQTerm (MTerm.Or xs) = TermC.QTerm11'or $ iNeToVec xs
serializeQTerm (MTerm.And xs) = TermC.QTerm11'and $ iNeToVec xs

deserializeQTerm :: TermC.QTerm11 -> MTerm.Term Void Int Int
deserializeQTerm TermC.QTerm11'litTrue = MTerm.LTrue
deserializeQTerm (TermC.QTerm11'state q) = MTerm.State $ fromIntegral q
deserializeQTerm (TermC.QTerm11'or xs) = MTerm.Or $ iVecToNe xs
deserializeQTerm (TermC.QTerm11'and xs) = MTerm.And $ iVecToNe xs
deserializeQTerm (TermC.QTerm11'unknown' _) = error "unknown qterm"

hRead :: Handle -> IO (Afa Int)
hRead h = deserializeAfa <$> Capnp.hGetValue h Capnp.defaultLimit

deserializeAfa :: AfaC.BoolAfa -> Afa Int
deserializeAfa AfaC.BoolAfa{AfaC.aterms = aterms, AfaC.qterms = qterms, AfaC.states = states} =
  Afa
    { aterms = listArray' $ map deserializeBTerm $ V.toList aterms
    , qterms = listArray' $ map deserializeQTerm $ V.toList qterms
    , states = listArray' $ map (map fromConjunct . V.toList) $ V.toList states
    , initState = 0
    }

fromConjunct (AfaC.Conjunct11 t a) = (fromMaybe1 t, fromMaybe1 a)

fromMaybe1 :: AfaC.Maybe1 -> Maybe Int
fromMaybe1 AfaC.Maybe1'nothing = Nothing
fromMaybe1 (AfaC.Maybe1'just a) = Just $ fromIntegral a
fromMaybe1 (AfaC.Maybe1'unknown' _) = error "unknown maybe"
