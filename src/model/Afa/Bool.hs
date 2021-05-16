{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Afa.Bool where

import Debug.Trace

import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Foldable
import Control.Monad.Free
import Control.Arrow
import Data.Traversable
import Control.Monad.Reader
import Data.Array
import Data.Array.ST
import Data.Array.Unsafe
import Data.Monoid (Any(..), Sum(..))
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.NoCons
import Control.RecursionSchemes.Utils.HashCons
import Control.Lens
import Control.Monad.ST
import qualified Control.Monad.ST.Lazy as LST
import Data.Fix
import Data.Functor.Compose
import Data.Hashable
import Data.Tuple

import Afa hiding (simplifyAll)
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Mix.Simplify as MTerm
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Bool.Simplify as BTerm
import Afa.Lib.Free
import Afa.Lib.LiftArray
import Afa.Lib
  (listArray', (>&>), nonemptyCanonicalizeWith, eixMappedGs, DumbCount(..))


data BoolAfa boolTerms afa = BoolAfa
  { boolTerms :: !boolTerms
  , afa :: !afa
  }
  deriving (Show, Eq)


type BoolTermIFree p = Free (BTerm.Term p) Int
type BoolAfaSwallowed p = BoolAfa
  (Array Int (BoolTermIFree p))
  (AfaSwallowed (BoolTermIFree p))
type BoolAfaUnswallowed p = BoolAfa
  (Array Int (BTerm.Term p Int))
  (AfaUnswallowed Int)


reorderStates' :: BoolAfaUnswallowed p -> BoolAfaUnswallowed p
reorderStates' bafa = bafa{afa = reorderStates$ afa bafa}


simplifyAll :: forall p. (Eq p, Hashable p, Show p)
  => BoolAfaUnswallowed p -> Either Bool (BoolAfaUnswallowed p)
simplifyAll bafa = do
  (mterms2, states2, init2) <- simplifyStatesAndMixTs ixMap1 mterms1 states init
  let bafa' = BoolAfa bterms1 (Afa mterms2 states2 init2)
  if rangeSize (bounds states2) == rangeSize (bounds states)
  then Right bafa'
  else simplifyAll bafa'
  where
  BoolAfa bterms (Afa mterms states init) = separateStatelessBottoms bafa
  mgs = accumArray (\_ x -> x) mempty (bounds mterms)$ map (, Any True) (elems states)
  (ixMap1, bterms1, mterms1) = simplifyMixAndBoolTs mgs bterms mterms


simplifyMixAndBoolTs :: forall p q. (Eq p, Hashable p, Eq q, Hashable q)
  => Array Int Any
  -> Array Int (BTerm.Term p Int)
  -> Array Int (MTerm.Term Int q Int)
  -> ( Array Int (Either Bool Int)
     , Array Int (BTerm.Term p Int)
     , Array Int (MTerm.Term Int q Int)
     )
simplifyMixAndBoolTs mgs bterms mterms = closure ixMap bterms mterms
  where
  ixMap = listArray (bounds mterms)$ map Right [0..]
  cost ts = (length ts, sum$ fmap length ts)
  closure ixMap bterms mterms
    | cost mterms2 > cost mterms3 = closure ixMap3 bterms2 mterms3
    | otherwise = (ixMap2', bterms2, mterms2)
    where
    (ixMap1, bterms1, mterms1) = simplifyInitMixAndBoolTs mgs ixMap bterms mterms
    (ixMap2, bterms2, mterms2) = separatePositiveTops bterms1 mterms1
    ixMap2' = fmap (fmap (ixMap2!)) ixMap1
    (ixMap3, mterms3) = MTerm.simplifyDagUntilFixpoint mgs (ixMap2', mterms2)

simplifyInitMixAndBoolTs :: forall p q. (Eq p, Hashable p, Eq q, Hashable q)
  => Array Int Any
  -> Array Int (Either Bool Int)
  -> Array Int (BTerm.Term p Int)
  -> Array Int (MTerm.Term Int q Int)
  -> ( Array Int (Either Bool Int)
     , Array Int (BTerm.Term p Int)
     , Array Int (MTerm.Term Int q Int)
     )
simplifyInitMixAndBoolTs mgs ixMap bterms mterms = runST action where
  action :: forall s. ST s
    ( Array Int (Either Bool Int)
    , Array Int (BTerm.Term p Int)
    , Array Int (MTerm.Term Int q Int)
    )
  action = do
    (((_, bterms'), ixMap'), tList) <- runHashConsT$ do
      bgs'M <- newArray @(LSTArray s) (bounds bterms) mempty
      (mgs'M :: LSTArray s Int Any) <- unsafeThaw$ eixMappedGs mterms ixMap mgs
      runKleisli (second$ Kleisli unsafeFreeze) =<< hyloScanT00'
        (atBottom <$> unsafeFreeze bgs'M)
        (\t (bIxMap, _) -> (t, bIxMap))
        (modPT (arrayEncloser' bgs'M snd) (arrayEncloser mgs'M fst))
        mhylogebra
        mgs'M

    return (fmap (>>= (ixMap'!) >&> fst) ixMap, bterms', listArray' tList)

  atBottom = flip BTerm.simplifyDagUntilFixpoint (bInitIxMap, bterms)
    where bInitIxMap = listArray (bounds bterms)$ map Right [0..]

  modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }

  mhylogebra (!g, !i) = return
    ( MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunT = (g,), MTerm.mtfunP = (g,)} (mterms!i)
    , alg g
    )

  alg (Any False) _ = return$ error "accessing element without parents"
  alg _ !t = case modPT id pure t of
    Left !b -> return$ Left b
    Right !t -> case MTerm.simplify ((Many,) . getCompose . unFix . snd) fst t of
      Left !b -> return$ Left b
      Right (Left !it) -> return$ Right it
      Right (Right !t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)

-- to be able to cons them with boolterms
separateStatelessBottoms :: forall p. (Eq p, Hashable p)
  => BoolAfaUnswallowed p -> BoolAfaUnswallowed p
separateStatelessBottoms (BoolAfa bterms afa@Afa{terms=mterms, states=states}) =
  runST action where
  action :: forall s. ST s (BoolAfaUnswallowed p)
  action = do
    ((ixMap, mList), bList) <-
      runHashConsT$ do
        bixMap <- ($bterms)$ cataScanT' @(LSTArray s) traversed `traverseOf` hashCons'
        runNoConsT$ mterms & cataScanT' @(LLSTArray s) traversed `traverseOf` \case
          MTerm.State q -> (Nothing,) <$> nocons (MTerm.State q)
          MTerm.Predicate ((bixMap!) -> b) -> (Just b,) <$> nocons (MTerm.Predicate b)
          MTerm.LTrue -> handleStateless BTerm.LTrue
          MTerm.And bts -> case mapM fst bts of
            Nothing -> (Nothing,) <$> nocons (MTerm.And$ snd <$> bts)
            Just bs -> handleStateless$ BTerm.And bs
          MTerm.Or bts -> case mapM fst bts of
            Nothing -> (Nothing,) <$> nocons (MTerm.Or$ snd <$> bts)
            Just bs -> handleStateless$ BTerm.Or bs

    return$ BoolAfa
      (listArray' bList)
      afa{ terms = listArray' mList, states = fmap (snd . (ixMap!)) states }

  handleStateless bt = do
    ref <- lift$ hashCons' bt
    fmap (Just ref,)$ nocons$ MTerm.Predicate ref


-- to be able to flatten them with mixterms
separatePositiveTops :: forall p q. (Eq q, Hashable q)
  => Array Int (BTerm.Term p Int)
  -> Array Int (MTerm.Term Int q Int)
  -> (Array Int Int, Array Int (BTerm.Term p Int), Array Int (MTerm.Term Int q Int))
separatePositiveTops bterms mterms =
  runST action where
  action :: forall s. ST s
    (Array Int Int, Array Int (BTerm.Term p Int), Array Int (MTerm.Term Int q Int))
  action = do
    ((ixMap, mList), bList) <- runNoConsT$ runHashConsT$ do
      bgs <- newArray @(LLSTArray s) (bounds bterms) mempty
      bixMap <- unsafeFreeze =<< hyloScanTTerminal' traversed bhylogebra bgs
      ($mterms)$ traverseOf (cataScanT' @(LLSTArray s) traversed)$ \case
        MTerm.Predicate p -> either return (hashCons' . MTerm.Predicate)$ bixMap!p
        x -> hashCons' x

    return (ixMap, listArray' bList, listArray' mList)

  bhylogebra (g, i) = return
    ( (g',) <$> bterm
    , case g' of
        Any True -> fmap Right . lift . nocons .
          fmap (either (error "positive under negative") id)
        Any False -> \case
          BTerm.LTrue -> Left <$> hashCons' MTerm.LTrue
          BTerm.And ixs -> fmap Left$ do
            ixs' <- forM ixs$ either return (hashCons' . MTerm.Predicate)
            hashCons'$ MTerm.And$ nonemptyCanonicalizeWith id ixs'
          BTerm.Or ixs -> fmap Left$ do
            ixs' <- forM ixs$ either return (hashCons' . MTerm.Predicate)
            hashCons'$ MTerm.Or$ nonemptyCanonicalizeWith id ixs'
          _ -> error "cannot be positive"
    )
    where
    bterm = bterms!i
    g' = case bterm of
      BTerm.Not _ -> Any True
      BTerm.LFalse -> Any True
      BTerm.Predicate _ -> Any True
      _ -> g


-- TODO the frees are traversed thrice, we need a setter generator for frees
unswallow :: forall p. (Show p, Hashable p, Eq p) => BoolAfaSwallowed p -> BoolAfaUnswallowed p
unswallow BoolAfa{boolTerms=bterms, afa=afa@Afa{terms=mterms, states=transitions}} =
  runST action where
  action :: forall s. ST s (BoolAfaUnswallowed p)
  action = do
    bgs <- newArray @(STArray s) (bounds bterms) mempty
    mgs <- newArray @(STArray s) (bounds mterms) mempty

    ((transitions', mterms'), bterms') <- runNoConsT$ runNoConsT$ do
      trs <- for transitions$ mhylogebra (Any True)
      let encls = fmap (first$ uncurry$ MEncloser mgs bgs) trs
      lift$ lift$ for_ encls$ actionBefore . fst
      ixMaps <- traverseOf _2 unsafeFreeze =<< hyloScanT00'
        ( lift$ unsafeFreeze . snd =<< hyloScanT00'
            (return ()) const (bsetter1 (LiftArray bgs)) bhylogebra (LiftArray bgs)
        )
        (,)
        (msetter1 (LiftArray$ LiftArray mgs) (LiftArray$ LiftArray bgs))
        (\(g, i) -> mhylogebra g (mterms!i))
        (LiftArray$ LiftArray mgs)
      remappedTransitions <- lift$ lift$
        runReaderT ((traversed . _1) actionAfter encls) (swap ixMaps)
      traverse (\(t, alg) -> alg t) remappedTransitions

    return$ BoolAfa (listArray' bterms')
      afa{ terms = listArray' mterms', states = transitions'}

  ifG (Any True) action !x = action x
  ifG _ _ _ = return$ error "accessing element without parents"

  unfree !t = cataT (freeTraversal traversed) (either return nocons) t
  bhylogebra (!g, !i) = return ((g, bterms!i), ifG g unfree)

  bsetter1 bgs = \(!g, !t) -> ($t)$ traverse$ \j ->
    Enclosing (beforeP bgs g j) (afterPM j)

  msetter1 !mgs !bgs = \(!g, !t) -> ($t)$
    modPT (traverse$ \(!j) -> Enclosing (beforeP bgs g j) (afterP2 j))
    `freeModChilds` \(!i) -> Enclosing (beforeP mgs g i) (afterP1M i)

  mhylogebra !g !t = return
    ((g, t), ifG g$ cataT (freeTraversal$ modPT$ lift . unfree) (either return nocons))

modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }

type MixBoolTerm p = MixTermIFree (BoolTermIFree p)

data MEncloser arr (m :: * -> *) p = MEncloser
  !(arr Int Any) !(arr Int Any) !Any !(MixBoolTerm p)

instance (Monad m, MArray arr Any m) => Encloser
  (MEncloser arr m p) m (ReaderT (Array Int Int, Array Int Int) m) (MixBoolTerm p)
  where
  {-# NOINLINE actionBefore #-}
  actionBefore (MEncloser mgs bgs g t) = ($t)$ freeFor_
    ( \rec -> \case
      MTerm.Predicate !p -> for_ p (beforeP bgs g)
      MTerm.LTrue -> return ()
      MTerm.State !q -> return ()
      MTerm.And !xs -> for_ xs rec 
      MTerm.Or !xs -> for_ xs rec 
    )
    (beforeP mgs g)
  {-# NOINLINE actionAfter #-}
  actionAfter (MEncloser mgs bgs g t) = ($t)$
    freeModChilds (modPT$ traverse afterP2) afterP1

{-# NOINLINE beforeP #-}
beforeP !bgs !g !j = do
  !g0 <- unsafeRead bgs j
  let !g1 = g0 <> g
  unsafeWrite bgs j g1

{-# NOINLINE afterP2 #-}
afterP2 !j = asks snd <&> (!j)

{-# NOINLINE afterP1 #-}
afterP1 !j = asks fst <&> (!j)

{-# NOINLINE afterP1M #-}
afterP1M !j = asks fst >>= \bs -> lift$ unsafeRead bs j

{-# NOINLINE afterPM #-}
afterPM !j = ask >>= \bs -> lift$ unsafeRead bs j

swallow :: forall p. BoolAfaUnswallowed p -> BoolAfaSwallowed p
swallow BoolAfa{boolTerms=bterms, afa=afa@Afa{terms=mterms, states=transitions}} =
  runST action where
  action :: forall s. ST s (BoolAfaSwallowed p)
  action = do
    ((transitions', mterms'), bterms') <- runNoConsT$ do
      bgs <- newArray @(LSTArray s) (bounds bterms) mempty
      runNoConsT$ do
        mgs <- newArray @(LLSTArray s) (bounds mterms) mempty
        let Enclosing before after = for transitions$ arrayEncloser' mgs id . (Sum 1,)
        before
        ixMaps <- unsafeFreeze . snd =<< hyloScanT00'
          (lift$ hyloScanTTerminal' traversed bhylogebra bgs >>= unsafeFreeze)
          (,)
          (modPT (arrayEncloser' (LiftArray bgs) snd) (arrayEncloser mgs fst))
          mhylogebra
          mgs
        runReaderT after ixMaps

    return$ BoolAfa (listArray' bterms')
      afa{ terms = listArray' mterms', states = transitions'}

  alg 0 _ = return$ error "accessing element without parents"
  alg 1 t = return$ Free t
  alg _ tb = Pure<$> nocons (Free tb)

  modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }

  bhylogebra (g, i) = return ((g,) <$> bterms!i, alg g)
  mhylogebra (g, i) = return
    ( MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunT = (g,), MTerm.mtfunP = (g,)} (mterms!i)
    , alg g
    )
