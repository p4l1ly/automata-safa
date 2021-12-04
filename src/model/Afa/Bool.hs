{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Bool where

import Afa hiding (simplifyAll)
import Afa.Lib (
  DumbCount (..),
  eixMappedGs,
  listArray',
  nonemptyCanonicalizeWith,
  (>&>),
 )
import Afa.Lib.Free
import Afa.Lib.LiftArray
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Bool.Simplify as BTerm
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Mix.Simplify as MTerm
import Control.Applicative ((<|>))
import Control.Arrow
import Control.Lens
import Control.Monad.Free
import Control.Monad.Reader
import Control.Monad.ST
import qualified Control.Monad.ST.Lazy as LST
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.HashCons
import Control.RecursionSchemes.Utils.NoCons
import Data.Array
import Data.Array.Base (numElements, unsafeAccumArray, unsafeAt, unsafeRead, unsafeWrite)
import Data.Array.ST
import Data.Array.Unsafe
import Data.Fix
import Data.Foldable
import Data.Functor.Compose
import Data.Hashable
import Data.List (find)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Monoid (Any (..), Ap (..), Sum (..))
import Data.Traversable
import Data.Tuple
import Debug.Trace
import System.IO.Unsafe

data BoolAfa boolTerms afa = BoolAfa
  { boolTerms :: !boolTerms
  , afa :: !afa
  }
  deriving (Show, Eq)

type BoolTermIFree p = Free (BTerm.Term p) Int

type BoolAfaSwallowed p =
  BoolAfa
    (Array Int (BoolTermIFree p))
    (AfaSwallowed (BoolTermIFree p))

type BoolAfaUnswallowed p =
  BoolAfa
    (Array Int (BTerm.Term p Int))
    (AfaUnswallowed Int)

isValid :: Show p => BoolAfaUnswallowed p -> Maybe String
isValid (BoolAfa bterms (Afa mterms states init)) =
  foldr1
    (<|>)
    [ ("bterms " ++) . show <$> find (\(i, t) -> any (>= i) t) (assocs bterms)
    , fmap (("mterms " ++) . show) $
        flip find (assocs mterms) $ \(i, t) ->
          any (>= i) t || case t of
            MTerm.Predicate p -> not $ inRange (bounds bterms) p
            _ -> False
    , fmap (("states " ++) . show) $
        flip find (assocs states) $ \(i, t) ->
          not $ inRange (bounds mterms) t
    , if not $ inRange (bounds states) init then Just $ "init " ++ show init else Nothing
    ]

{-# INLINEABLE replaceLits #-}
replaceLits :: BoolAfaUnswallowed Int -> BoolAfaUnswallowed Int
replaceLits (BoolAfa bterms (Afa mterms states init)) =
  BoolAfa bterms'' (Afa mterms'' (states <&> (mixMap !)) init)
  where
    btermCount = numElements bterms
    (bixMap, bterms') = runST action
      where
        action :: forall s. ST s (Array Int Int, [BTerm.Term Int Int])
        action = runNoConsTFrom 4 $
          ($ bterms) $
            cataScanT' @(LSTArray s) traversed $ \case
              BTerm.LTrue -> return 2
              BTerm.LFalse -> return 3
              BTerm.And (i :| []) -> return i
              BTerm.Or (i :| []) -> return i
              t -> nocons t
    bterms'' =
      listArray' $
        [BTerm.Predicate 0, BTerm.Not 0, BTerm.Or $ 0 :| [1], BTerm.And $ 0 :| [1]]
          ++ bterms'

    (mixMap, mterms') = runST action
      where
        action :: forall s. ST s (Array Int Int, [MTerm.Term Int Int Int])
        action = runNoConsT $
          ($ mterms) $
            cataScanT' @(LSTArray s) traversed $ \case
              MTerm.LTrue -> nocons $ MTerm.Predicate 2
              MTerm.Predicate p -> nocons $ MTerm.Predicate (bixMap ! p)
              MTerm.And (i :| []) -> return i
              MTerm.Or (i :| []) -> return i
              t -> nocons t
    mterms'' = listArray' mterms'

{-# INLINEABLE reorderStates' #-}
reorderStates' :: BoolAfaUnswallowed p -> BoolAfaUnswallowed p
reorderStates' bafa = bafa{afa = reorderStates $ afa bafa}

hashConsBoolAfa ::
  forall p.
  (Eq p, Hashable p, Show p) =>
  BoolAfaUnswallowed p ->
  BoolAfaUnswallowed p
hashConsBoolAfa (BoolAfa bterms (Afa mterms states init)) = runST action
  where
    action :: forall s. ST s (BoolAfaUnswallowed p)
    action = do
      (bIxMap, bterms') <- runHashConsT $ cataScanT' @(LSTArray s) traversed hashCons' bterms
      let mtraversed rec = MTerm.modChilds MTerm.pureChildMod{MTerm.lT = rec, MTerm.lP = return . (bIxMap !)}
      (mIxMap, mterms') <- runHashConsT $ cataScanT' @(LSTArray s) mtraversed hashCons' mterms
      return $
        BoolAfa (listArray' bterms') $
          Afa (listArray' mterms') ((mIxMap !) <$> states) init

{-# INLINEABLE simplifyAll #-}
simplifyAll ::
  forall p.
  (Eq p, Hashable p, Show p) =>
  BoolAfaUnswallowed p ->
  Either Bool (BoolAfaUnswallowed p)
simplifyAll bafa = do
  (mterms2, states2, init2) <- simplifyStatesAndMixTs ixMap1 mterms1 states init
  let bafa' = BoolAfa bterms1 (Afa mterms2 states2 init2)
  if rangeSize (bounds states2) == rangeSize (bounds states)
    then Right bafa'
    else simplifyAll bafa'
  where
    BoolAfa bterms (Afa mterms states init) = separateStatelessBottoms bafa
    mgs = unsafeAccumArray (\_ x -> x) mempty (bounds mterms) $ map (,Any True) (elems states)
    (ixMap1, bterms1, mterms1) = simplifyMixAndBoolTs mgs bterms mterms

{-# INLINEABLE simplifyMixAndBoolTs #-}
simplifyMixAndBoolTs ::
  forall p q.
  (Eq p, Hashable p, Eq q, Hashable q) =>
  Array Int Any ->
  Array Int (BTerm.Term p Int) ->
  Array Int (MTerm.Term Int q Int) ->
  ( Array Int (Either Bool Int)
  , Array Int (BTerm.Term p Int)
  , Array Int (MTerm.Term Int q Int)
  )
simplifyMixAndBoolTs mgs bterms mterms = closure ixMap bterms mterms
  where
    ixMap = listArray (bounds mterms) $ map Right [0 ..]
    cost ts = (length ts, sum $ fmap length ts)
    closure ixMap bterms mterms
      | cost mterms2 > cost mterms3 = closure ixMap3 bterms2 mterms3
      | otherwise = (ixMap2', bterms2, mterms2)
      where
        (ixMap1, bterms1, mterms1) = simplifyInitMixAndBoolTs mgs ixMap bterms mterms
        (ixMap2, bterms2, mterms2) = separatePositiveTops bterms1 mterms1
        ixMap2' = fmap (fmap (ixMap2 `unsafeAt`)) ixMap1
        (ixMap3, mterms3) = MTerm.simplifyDagUntilFixpoint mgs (ixMap2', mterms2)

{-# INLINEABLE simplifyInitMixAndBoolTs #-}
simplifyInitMixAndBoolTs ::
  forall p q.
  (Eq p, Hashable p, Eq q, Hashable q) =>
  Array Int Any ->
  Array Int (Either Bool Int) ->
  Array Int (BTerm.Term p Int) ->
  Array Int (MTerm.Term Int q Int) ->
  ( Array Int (Either Bool Int)
  , Array Int (BTerm.Term p Int)
  , Array Int (MTerm.Term Int q Int)
  )
simplifyInitMixAndBoolTs mgs ixMap bterms mterms = runST action
  where
    action ::
      forall s.
      ST
        s
        ( Array Int (Either Bool Int)
        , Array Int (BTerm.Term p Int)
        , Array Int (MTerm.Term Int q Int)
        )
    action = do
      (((_, bterms'), ixMap'), tList) <- runHashConsT $ do
        bgs'M <- newArray @(LSTArray s) (bounds bterms) mempty
        (mgs'M :: LSTArray s Int Any) <- unsafeThaw $ eixMappedGs mterms ixMap mgs
        runKleisli (second $ Kleisli unsafeFreeze)
          =<< hyloScanTFast @(LSTArray s)
            (atBottom <$> unsafeFreeze bgs'M)
            ( \g i ->
                void $
                  getAp $
                    MTerm.appMTFol
                      MTerm.mtfol0
                        { MTerm.mtfolT = \j -> Ap $ unsafeRead mgs'M j >>= unsafeWrite mgs'M j . (<> g)
                        , MTerm.mtfolP = \j -> Ap $ unsafeRead bgs'M j >>= unsafeWrite bgs'M j . (<> g)
                        }
                      (mterms `unsafeAt` i)
            )
            ( \ixMap' (bterms', _) g i ->
                alg g
                  =<< MTerm.appMTTra
                    MTerm.mttra0
                      { MTerm.mttraT = unsafeRead ixMap'
                      , MTerm.mttraP = \j -> return $ bterms' `unsafeAt` j
                      }
                    (mterms `unsafeAt` i)
            )
            mgs'M

      return (fmap (>>= unsafeAt @Array ixMap' >&> fst) ixMap, bterms', listArray' tList)

    atBottom = flip BTerm.simplifyDagUntilFixpoint (bInitIxMap, bterms)
      where
        bInitIxMap = listArray (bounds bterms) $ map Right [0 ..]

    {-# INLINE modPT #-}
    modPT lP lT = MTerm.modChilds MTerm.pureChildMod{MTerm.lT = lT, MTerm.lP = lP}

    alg (Any False) _ = return $ error "accessing element without parents"
    alg _ !t = case modPT id pure t of
      Left !b -> return $ Left b
      Right !t -> case MTerm.simplify ((Many,) . getCompose . unFix . snd) fst t of
        Left !b -> return $ Left b
        Right (Left !it) -> return $ Right it
        Right (Right !t) -> Right . (,Fix $ Compose t) <$> hashCons' (fmap fst t)

-- to be able to cons them with boolterms
{-# INLINEABLE separateStatelessBottoms #-}
separateStatelessBottoms ::
  forall p.
  (Eq p, Hashable p) =>
  BoolAfaUnswallowed p ->
  BoolAfaUnswallowed p
separateStatelessBottoms (BoolAfa bterms afa@Afa{terms = mterms, states = states}) =
  runST action
  where
    action :: forall s. ST s (BoolAfaUnswallowed p)
    action = do
      ((ixMap, mList), bList) <-
        runHashConsT $ do
          bixMap <- ($ bterms) $ cataScanT' @(LSTArray s) traversed `traverseOf` hashCons'
          runNoConsT $
            mterms & cataScanT' @(LLSTArray s) traversed `traverseOf` \case
              MTerm.State q -> (Nothing,) <$> nocons (MTerm.State q)
              MTerm.Predicate (unsafeAt bixMap -> b) -> (Just b,) <$> nocons (MTerm.Predicate b)
              MTerm.LTrue -> handleStateless BTerm.LTrue
              MTerm.And bts -> case mapM fst bts of
                Nothing -> (Nothing,) <$> nocons (MTerm.And $ snd <$> bts)
                Just bs -> handleStateless $ BTerm.And bs
              MTerm.Or bts -> case mapM fst bts of
                Nothing -> (Nothing,) <$> nocons (MTerm.Or $ snd <$> bts)
                Just bs -> handleStateless $ BTerm.Or bs

      return $
        BoolAfa
          (listArray' bList)
          afa{terms = listArray' mList, states = fmap (snd . unsafeAt ixMap) states}

    handleStateless bt = do
      ref <- lift $ hashCons' bt
      fmap (Just ref,) $ nocons $ MTerm.Predicate ref

-- to be able to flatten them with mixterms
separatePositiveTops ::
  forall p q.
  (Eq q, Hashable q) =>
  Array Int (BTerm.Term p Int) ->
  Array Int (MTerm.Term Int q Int) ->
  (Array Int Int, Array Int (BTerm.Term p Int), Array Int (MTerm.Term Int q Int))
separatePositiveTops bterms mterms =
  runST action
  where
    action ::
      forall s.
      ST
        s
        (Array Int Int, Array Int (BTerm.Term p Int), Array Int (MTerm.Term Int q Int))
    action = do
      ((ixMap, mList), bList) <- runNoConsT $
        runHashConsT $ do
          bgs <- newArray @(LLSTArray s) (bounds bterms) mempty
          bixMap <- unsafeFreeze =<< hyloScanTTerminal' traversed bhylogebra bgs
          ($ mterms) $
            traverseOf (cataScanT' @(LLSTArray s) traversed) $ \case
              MTerm.Predicate p -> either return (hashCons' . MTerm.Predicate) $ unsafeAt @Array bixMap p
              x -> hashCons' x

      return (ixMap, listArray' bList, listArray' mList)

    bhylogebra (g, i) =
      return
        ( (g',) <$> bterm
        , case g' of
            Any True ->
              fmap Right . lift . nocons
                . fmap (either (error "positive under negative") id)
            Any False -> \case
              BTerm.LTrue -> Left <$> hashCons' MTerm.LTrue
              BTerm.And ixs -> fmap Left $ do
                ixs' <- forM ixs $ either return (hashCons' . MTerm.Predicate)
                hashCons' $ MTerm.And $ nonemptyCanonicalizeWith id ixs'
              BTerm.Or ixs -> fmap Left $ do
                ixs' <- forM ixs $ either return (hashCons' . MTerm.Predicate)
                hashCons' $ MTerm.Or $ nonemptyCanonicalizeWith id ixs'
              _ -> error "cannot be positive"
        )
      where
        bterm = bterms `unsafeAt` i
        g' = case bterm of
          BTerm.Not _ -> Any True
          BTerm.LFalse -> Any True
          BTerm.Predicate _ -> Any True
          _ -> g

-- TODO the frees are traversed thrice, we need a setter generator for frees
{-# INLINEABLE unswallow #-}
unswallow :: forall p. (Show p, Hashable p, Eq p) => BoolAfaSwallowed p -> BoolAfaUnswallowed p
unswallow BoolAfa{boolTerms = bterms, afa = afa@Afa{terms = mterms, states = transitions}} =
  runST action
  where
    action :: forall s. ST s (BoolAfaUnswallowed p)
    action = do
      bgs <- newArray @(STArray s) (bounds bterms) mempty
      mgs <- newArray @(STArray s) (bounds mterms) mempty

      ((transitions', mterms'), bterms') <- runNoConsT $
        runNoConsT $ do
          trs <- for transitions $ mhylogebra (Any True)
          let encls = fmap (first $ uncurry $ MEncloser mgs bgs) trs
          lift $ lift $ for_ encls $ actionBefore . fst
          ixMaps <-
            traverseOf _2 unsafeFreeze
              =<< hyloScanT00'
                ( lift $
                    unsafeFreeze . snd
                      =<< hyloScanT00'
                        (return ())
                        const
                        (bsetter1 (LiftArray bgs))
                        bhylogebra
                        (LiftArray bgs)
                )
                (,)
                (msetter1 (LiftArray $ LiftArray mgs) (LiftArray $ LiftArray bgs))
                (\(g, i) -> mhylogebra g (mterms `unsafeAt` i))
                (LiftArray $ LiftArray mgs)
          remappedTransitions <-
            lift $
              lift $
                runReaderT ((traversed . _1) actionAfter encls) (swap ixMaps)
          traverse (\(t, alg) -> alg t) remappedTransitions

      return $
        BoolAfa
          (listArray' bterms')
          afa{terms = listArray' mterms', states = transitions'}

    ifG (Any True) action !x = action x
    ifG _ _ _ = return $ error "accessing element without parents"

    unfree !t = cataT (freeTraversal traversed) (either return nocons) t
    bhylogebra (!g, !i) = return ((g, bterms `unsafeAt` i), ifG g unfree)

    bsetter1 bgs = \(!g, !t) -> ($ t) $
      traverse $ \j ->
        Enclosing (beforeP bgs g j) (afterPM j)

    msetter1 !mgs !bgs = \(!g, !t) ->
      ($ t) $
        modPT (traverse $ \(!j) -> Enclosing (beforeP bgs g j) (afterP2 j))
          `freeModChilds` \(!i) -> Enclosing (beforeP mgs g i) (afterP1M i)

    mhylogebra !g !t =
      return
        ((g, t), ifG g $ cataT (freeTraversal $ modPT $ lift . unfree) (either return nocons))

modPT lP lT = MTerm.modChilds MTerm.pureChildMod{MTerm.lT = lT, MTerm.lP = lP}

type MixBoolTerm p = MixTermIFree (BoolTermIFree p)

data MEncloser arr (m :: * -> *) p
  = MEncloser
      !(arr Int Any)
      !(arr Int Any)
      !Any
      !(MixBoolTerm p)

instance
  (Monad m, MArray arr Any m) =>
  Encloser
    (MEncloser arr m p)
    m
    (ReaderT (Array Int Int, Array Int Int) m)
    (MixBoolTerm p)
  where
  {-# NOINLINE actionBefore #-}
  actionBefore (MEncloser mgs bgs g t) =
    ($ t) $
      freeFor_
        ( \rec -> \case
            MTerm.Predicate !p -> for_ p (beforeP bgs g)
            MTerm.LTrue -> return ()
            MTerm.State !q -> return ()
            MTerm.And !xs -> for_ xs rec
            MTerm.Or !xs -> for_ xs rec
        )
        (beforeP mgs g)
  {-# NOINLINE actionAfter #-}
  actionAfter (MEncloser mgs bgs g t) =
    ($ t) $
      freeModChilds (modPT $ traverse afterP2) afterP1

{-# NOINLINE beforeP #-}
beforeP !bgs !g !j = do
  !g0 <- unsafeRead bgs j
  let !g1 = g0 <> g
  unsafeWrite bgs j g1

{-# NOINLINE afterP2 #-}
afterP2 !j = asks snd <&> (! j)

{-# NOINLINE afterP1 #-}
afterP1 !j = asks fst <&> (! j)

{-# NOINLINE afterP1M #-}
afterP1M !j = asks fst >>= \bs -> lift $ unsafeRead bs j

{-# NOINLINE afterPM #-}
afterPM !j = ask >>= \bs -> lift $ unsafeRead bs j

{-# INLINEABLE swallow #-}
swallow :: forall p. BoolAfaUnswallowed p -> BoolAfaSwallowed p
swallow BoolAfa{boolTerms = bterms, afa = afa@Afa{terms = mterms, states = transitions}} =
  runST action
  where
    action :: forall s. ST s (BoolAfaSwallowed p)
    action = do
      ((transitions', mterms'), bterms') <- runNoConsT $ do
        bgs <- newArray @(LSTArray s) (bounds bterms) mempty
        runNoConsT $ do
          mgs <- newArray @(LLSTArray s) (bounds mterms) mempty
          let Enclosing before after = for transitions $ arrayEncloser' mgs id . (Sum 1,)
          before
          ixMaps <-
            unsafeFreeze . snd
              =<< hyloScanT00'
                (lift $ hyloScanTTerminal' traversed bhylogebra bgs >>= unsafeFreeze)
                (,)
                (modPT (arrayEncloser' (LiftArray bgs) snd) (arrayEncloser mgs fst))
                mhylogebra
                mgs
          runReaderT after ixMaps

      return $
        BoolAfa
          (listArray' bterms')
          afa{terms = listArray' mterms', states = transitions'}

    alg _ 0 _ = return $ error "accessing element without parents"
    alg _ 1 t = return $ Free t
    alg isTerminal _ t
      | isTerminal t = return $ Free t
      | otherwise = Pure <$> nocons (Free t)

    modPT lP lT = MTerm.modChilds MTerm.pureChildMod{MTerm.lT = lT, MTerm.lP = lP}

    bIsTerminal (BTerm.Predicate _) = True
    bIsTerminal BTerm.LTrue = True
    bIsTerminal BTerm.LFalse = True
    bIsTerminal _ = False

    mIsTerminal MTerm.LTrue = True
    mIsTerminal (MTerm.State _) = True
    mIsTerminal (MTerm.Predicate (Pure _)) = True
    mIsTerminal (MTerm.Predicate (Free p)) = bIsTerminal p
    mIsTerminal _ = False

    bhylogebra (g, i) = return ((g,) <$> bterms `unsafeAt` i, alg bIsTerminal g)
    mhylogebra (g, i) =
      return
        ( MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunT = (g,), MTerm.mtfunP = (g,)} (mterms `unsafeAt` i)
        , alg mIsTerminal g
        )
