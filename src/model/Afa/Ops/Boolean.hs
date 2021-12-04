{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Ops.Boolean (
  intersection,
  union,
  complementUnsafeShallow,
  complementUnsafeDeep,
) where

import Afa
import Afa.Bool
import Afa.Lib
import Afa.Lib.LiftArray
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm
import Control.Lens
import Control.Monad.ST
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons
import Data.Array
import Data.Array.Base (numElements)
import Data.Array.Unsafe
import Data.List.NonEmpty (NonEmpty ((:|)))

positiveOp ::
  (NonEmpty Int -> MTerm.Term Int Int Int) ->
  BoolAfaUnswallowed p ->
  BoolAfaUnswallowed p ->
  BoolAfaUnswallowed p
positiveOp
  op
  (BoolAfa bterms1 (Afa mterms1 states1 init1))
  (BoolAfa bterms2 (Afa mterms2 states2 init2)) =
    BoolAfa bterms (Afa mterms states (states1Count + states2Count))
    where
      bterms1Count = numElements bterms1
      bterms2Count = numElements bterms2
      bterms =
        listArray (0, bterms1Count + bterms2Count - 1) $
          elems bterms1 ++ map (fmap (+ bterms1Count)) (elems bterms2)

      mterms1Count = numElements mterms1
      mterms2Count = numElements mterms2
      mterms =
        listArray (0, mterms1Count + mterms2Count) $
          elems mterms1
            ++ map
              ( MTerm.appMTFun
                  MTerm.MTFun
                    { MTerm.mtfunP = (+ bterms1Count)
                    , MTerm.mtfunQ = (+ states1Count)
                    , MTerm.mtfunT = (+ mterms1Count)
                    }
              )
              (elems mterms2)
            ++ [op $ (states1 ! init1) :| [states2 ! init2 + mterms1Count]]

      states1Count = numElements states1
      states2Count = numElements states2
      states =
        listArray (0, states1Count + states2Count) $
          elems states1
            ++ map (+ mterms1Count) (elems states2)
            ++ [mterms1Count + mterms2Count]

intersection :: BoolAfaUnswallowed p -> BoolAfaUnswallowed p -> BoolAfaUnswallowed p
intersection = positiveOp MTerm.And

union :: BoolAfaUnswallowed p -> BoolAfaUnswallowed p -> BoolAfaUnswallowed p
union = positiveOp MTerm.Or

complementUnsafeShallow :: BoolAfaUnswallowed p -> BoolAfaUnswallowed p
complementUnsafeShallow (BoolAfa bterms1 (Afa mterms1 states1 init1)) =
  BoolAfa bterms (Afa mterms states1 init1)
  where
    bterms1Count = numElements bterms1
    bterms =
      listArray (0, 2 * bterms1Count - 1) $
        elems bterms1 ++ map BTerm.Not [0 .. bterms1Count - 1]

    mterms = fmap (dualize . MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunP = (+ bterms1Count)}) mterms1

    dualize (MTerm.And xs) = MTerm.Or xs
    dualize (MTerm.Or xs) = MTerm.And xs
    dualize x = x

complementUnsafeDeep :: forall p. BoolAfaUnswallowed p -> BoolAfaUnswallowed p
complementUnsafeDeep (BoolAfa bterms1 (Afa mterms1 states1 init1)) =
  BoolAfa (listArray' bterms) (Afa mterms states1 init1)
  where
    (ixMap, bterms) = runST action
      where
        action :: forall s. ST s (Array Int Int, [BTerm.Term p Int])
        action = runNoConsT $ cataScanT' @(LSTArray s) traversed alg bterms1
          where
            alg x@(BTerm.Predicate p) = nocons x >>= nocons . BTerm.Not
            alg x = nocons $ bdualize x

    mterms = fmap (mdualize . MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunP = (ixMap !)}) mterms1

    mdualize (MTerm.And xs) = MTerm.Or xs
    mdualize (MTerm.Or xs) = MTerm.And xs
    mdualize x = x

    bdualize (BTerm.And xs) = BTerm.Or xs
    bdualize (BTerm.Or xs) = BTerm.And xs
    bdualize x = x
