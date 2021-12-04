{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.Capnp.Range16Nfa where

import qualified Capnp
import qualified Capnp.Gen.Afa.Model.Separated.Pure as AfaC
import qualified Capnp.GenHelpers.ReExports.Data.Vector as V
import Control.Arrow
import Control.Monad.Free
import Data.Array
import Data.Bits
import Data.Foldable
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Void
import System.IO

import Afa
import Afa.Bool
import Afa.Convert.Capnp.Afa (iNeToVec, serializeBTerm, varCount)
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

hReadNfa :: Handle -> IO (BoolAfaUnswallowed Int)
hReadNfa h = deserializeNfa <$> Capnp.hGetValue h maxBound

deserializeNfa :: AfaC.Range16Nfa -> BoolAfaUnswallowed Int
deserializeNfa (AfaC.Range16Nfa states (fromIntegral -> initial) finals) =
  unswallow
    BoolAfa
      { boolTerms =
          listArray (0, 35) $
            map (Free . BTerm.Predicate) [1 .. 16]
              ++ map (Free . BTerm.Not . Pure) [0 .. 15]
              ++ [Free $ BTerm.Predicate 0, Free $ BTerm.Not $ Pure 32, Free BTerm.LFalse, Free BTerm.LTrue]
      , afa =
          Afa
            { initState = qcount
            , terms = listArray (0, -1) []
            , states =
                listArray (0, qcount) $
                  (++ [initState']) $
                    toList states <&> \(toList -> transitions) ->
                      mkOr $
                        transitions
                          <&> \(AfaC.ConjunctR16Q (toList -> ranges) (fromIntegral -> state)) ->
                            Free $
                              MTerm.And $
                                let guard = Free $ MTerm.Predicate $ mkOrB $ map convertRange ranges
                                 in if finalMask ! state
                                      then guard :| [Free $ MTerm.Or $ finalSym :| [mkState state]]
                                      else guard :| [nonfinalSym, mkState state]
            }
      }
  where
    sym = Free . MTerm.Predicate . Pure
    finalSym = sym 32
    nonfinalSym = sym 33
    falseSym = sym 34
    mkOr = maybe falseSym (Free . MTerm.Or) . nonEmpty
    mkOrB = maybe (Pure 34) (Free . BTerm.Or) . nonEmpty
    mkState = Free . MTerm.State
    qcount = V.length states
    finalMask =
      accumArray (\_ _ -> True) False (0, qcount - 1) $
        map (\i -> (fromIntegral i, ())) $ toList finals
    initState' =
      if finalMask ! initial
        then Free $ MTerm.Or $ finalSym :| [mkState initial]
        else Free $ MTerm.And $ nonfinalSym :| [mkState initial]

convertRange :: AfaC.Range16 -> BoolTermIFree Int
convertRange (AfaC.Range16 0x0000 0xffff) = Pure 35
convertRange (AfaC.Range16 begin end) = Free $ BTerm.And $ diff' :| map byBeg common
  where
    {-# INLINE getBeg #-}
    getBeg = testBit begin
    {-# INLINE getEnd #-}
    getEnd = testBit end

    pos i = Pure i
    neg i = Pure $ i + 16
    byBeg i = if getBeg i then pos i else neg i
    (common, diff) = span (\i -> getBeg i == getEnd i) [15, 14 .. 0]

    diff' = case diff of
      [] -> Pure 35
      x : rest ->
        Free $
          BTerm.Or $
            Free (BTerm.And $ neg x :| [gte rest])
              :| [Free (BTerm.And $ pos x :| [lte rest])]

    gte (x : rest) =
      if getBeg x
        then Free $ BTerm.And $ pos x :| [gte rest]
        else Free $ BTerm.Or $ pos x :| [gte rest]
    gte [] = Pure 35

    lte (x : rest) =
      if getEnd x
        then Free $ BTerm.Or $ neg x :| [lte rest]
        else Free $ BTerm.And $ neg x :| [lte rest]
    lte [] = Pure 35
