{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.Capnp.Range16Nfa where

import qualified Capnp
import qualified Capnp.Gen.Afa.Model.Separated as AfaC
import Control.Arrow
import Control.Monad.Free
import Data.Array
import Data.Bits hiding (And (..))
import Data.Foldable
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import qualified Data.List.NonEmpty as NE
import qualified Data.Vector as V
import Data.Void
import Data.Word
import System.IO

import Afa
import Afa.Bool
import Afa.Convert.Capnp.Afa (iNeToVec, serializeBTerm, varCount)
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

import Afa.Finalful.STerm
import qualified Afa.IORef
import Data.Composition ((.:))
import Data.Fix (Fix (Fix))
import Data.Traversable (for)
import DepDict (DepDict ((:|:)), ToConstraint)
import qualified DepDict as D
import Shaper
import Shaper.Helpers (BuildD, buildFix)
import TypeDict (Named (Name), TypeDict (End, (:+:)), d, d', g')

hReadNfa :: Handle -> IO (BoolAfaUnswallowed Int)
hReadNfa h = deserializeNfa <$> Capnp.hGetParsed h maxBound

hReadNfaRaw :: Handle -> IO (AfaC.Parsed AfaC.Range16Nfa)
hReadNfaRaw h = Capnp.hGetParsed h maxBound

deserializeNfa :: AfaC.Parsed AfaC.Range16Nfa -> BoolAfaUnswallowed Int
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

convertRange :: Range16 -> BoolTermIFree Int
convertRange (AfaC.Range16 0x0000 0xffff) = Pure 35 -- True
convertRange (AfaC.Range16 begin end) = Free $ BTerm.And $ diff' :| map byBeg common
  where
    {-# INLINE getBeg #-}
    getBeg = testBit begin -- get bit from the range's start
    {-# INLINE getEnd #-}
    getEnd = testBit end -- get bit from the range's end
    pos i = Pure i -- positive variable: v_i
    neg i = Pure $ i + 16 -- negative variable: NOT(v_i)
    byBeg i = if getBeg i then pos i else neg i
    (common, diff) = span (\i -> getBeg i == getEnd i) [15, 14 .. 0]

    diff' = case diff of
      [] -> Pure 35 -- True
      x : rest ->
        Free $
          BTerm.Or $
            Free (BTerm.And $ neg x :| [gte rest])
              :| [Free (BTerm.And $ pos x :| [lte rest])]

    gte (x : rest) =
      if getBeg x
        then Free $ BTerm.And $ pos x :| [gte rest]
        else Free $ BTerm.Or $ pos x :| [gte rest]
    gte [] = Pure 35 -- True
    lte (x : rest) =
      if getEnd x
        then Free $ BTerm.Or $ neg x :| [lte rest]
        else Free $ BTerm.And $ neg x :| [lte rest]
    lte [] = Pure 35 -- True

convertRange2 :: Range16 -> Fix (Term q Word8)
convertRange2 (AfaC.Range16 0x0000 0xffff) = Fix LTrue
convertRange2 (AfaC.Range16 begin end) = foldr (Fix .: And . byBeg) diff' common
  where
    {-# INLINE getBeg #-}
    getBeg i = testBit begin (fromIntegral i)
    {-# INLINE getEnd #-}
    getEnd i = testBit end (fromIntegral i)
    (common, diff) = span (\i -> getBeg i == getEnd i) [15, 14 .. 0]
    byBeg i = if getBeg i then Fix $ Var i else Fix $ Not $ Fix $ Var i

    diff' = case diff of
      [] -> Fix LTrue
      (x :: Word8) : rest ->
        Fix $
          Or
            (Fix $ And (Fix $ Not $ Fix $ Var x) (gte rest))
            (Fix $ And (Fix $ Var x) (lte rest))

    gte (x : rest) =
      if getBeg x
        then Fix $ And (Fix $ Var x) (gte rest)
        else Fix $ Or (Fix $ Var x) (gte rest)
    gte [] = Fix LTrue

    lte (x : rest) =
      if getEnd x
        then Fix $ Or (Fix $ Not $ Fix $ Var x) (lte rest)
        else Fix $ And (Fix $ Not $ Fix $ Var x) (lte rest)
    lte [] = Fix LTrue

type DeserializeNfaA d r =
  DeserializeNfaA1 d (Name "termF" (Term Word32 (AfaC.Parsed AfaC.Range16)) :+: End) r
type DeserializeNfaA1 d d' r =
  DeserializeNfaA2 d (Name "buildTree" (Mk (MfnK ([g'|termF|] r) r) [d|buildTree|]) :+: d')
type DeserializeNfaA2 d d' = Name "buildD" (Name "build" [d'|buildTree|] :+: d) :+: d'
type DeserializeNfaD_ d m d' r =
  D.Name "aliases" (d' ~ DeserializeNfaA d r)
    :|: D.Name "build" (MonadFn [d'|buildTree|] m)
    :|: D.Name "buildD" (BuildD [g'|buildD|] [g'|termF|] r m)
    :|: D.End
deserializeNfa2 ::
  forall (d :: TypeDict) r m (d' :: TypeDict).
  ToConstraint (DeserializeNfaD_ d m d' r) =>
  AfaC.Parsed AfaC.Range16Nfa ->
  m (r, V.Vector Word32, (Int, Int -> Word32, Int -> V.Vector (r, r), Word32 -> Int))
deserializeNfa2 (AfaC.Range16Nfa states init finals) = do
  initR <- [d'|monadfn|buildTree|] (State init)
  states' <- for states \ts ->
    for ts \(AfaC.ConjunctR16Q ranges q) -> do
      let a = foldr (Fix .: Or . Fix . Var) (Fix LFalse) ranges
      ar <- buildFix @[g'|buildD|] a
      qr <- [d'|monadfn|buildTree|] (State q)
      return (ar, qr)
  return (initR, finals, (V.length states, fromIntegral, (states' V.!), fromIntegral))

deserializeToIORef ::
  forall q v r r' d.
  ( r ~ Afa.IORef.Ref (Term Word32 Range16)
  , d ~ Afa.IORef.IORefRemoveFinalsD Word32 Range16 r r'
  ) =>
  AfaC.Parsed AfaC.Range16Nfa ->
  IO (r, V.Vector Word32, (Int, Int -> Word32, Int -> V.Vector (r, r), Word32 -> Int))
deserializeToIORef = deserializeNfa2 @d

convertRangeIORef ::
  forall q v r r' d buildD derange.
  ( r ~ Afa.IORef.Ref (Term q Range16)
  , r' ~ Afa.IORef.Ref (Term q Word8)
  , d ~ Afa.IORef.IORefRemoveFinalsD Word32 Range16 r r'
  , buildD ~ (Name "build" (Mk (MfnK (Term q Word8 r') r') [d|buildTree|]) :+: d)
  , derange ~ Mk (FRecK r r' (VarTra IO Range16 q Word8 r')) [d|funr|]
  ) =>
  (r, r, (Int, Int -> q, Int -> r, q -> Int)) ->
  IO (r', r', (Int, Int -> q, Int -> r', q -> Int))
convertRangeIORef (init, final, (qCount, i2q, i2r, q2i)) = do
  let build (Fix f) = traverse (buildFix @buildD) f
  let fun = VarTra $ build . convertRange2
  derange <- funRecur @derange fun
  init' <- derange init
  final' <- derange final
  i2rArr <- listArray (0, qCount - 1) <$> mapM (derange . i2r) [0 .. qCount - 1]
  return (init', final', (qCount, i2q, (i2rArr !), q2i))

type Range16 = AfaC.Parsed AfaC.Range16
