{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

module Afa.Bool where

import GHC.Exts (sortWith, groupWith)
import Data.List (partition)
import Data.Either
import Control.Arrow
import Data.Traversable
import Control.Monad.Reader
import Data.Array
import Data.Array.ST
import Data.Array.Unsafe
import Data.Monoid (Any(..), Sum(..), Endo(..))
import Control.RecursionSchemes.Lens
import Control.Lens
import Control.Monad.ST
import Data.Fix
import Data.Functor.Compose
import Data.Hashable

import Afa
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Mix.Simplify as MTerm
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Bool.Simplify as BTerm
import Afa.Lib.Tree
import Afa.Lib.LiftArray
import Afa.Lib (listArray', (>&>), nonemptyCanonicalizeWith, eixMappedGs)


data BoolAfa boolTerms afa = BoolAfa
  { boolTerms :: boolTerms
  , afa :: afa
  }
  deriving (Show, Eq)


-- TODO Tree is actually Free
type BoolTermITree p = Tree (BTerm.Term p) Int
type BoolAfaSwallowed p = BoolAfa
  (Array Int (BoolTermITree p))
  (AfaSwallowed (BoolTermITree p))
type BoolAfaUnswallowed p = BoolAfa
  (Array Int (BTerm.Term p Int))
  (AfaUnswallowed Int)


reorderStates' :: BoolAfaUnswallowed p -> BoolAfaUnswallowed p
reorderStates' bafa = bafa{afa = reorderStates$ afa bafa}


simplifyAll :: forall p. (Eq p, Hashable p)
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


-- TODO: This is not implemented in an idyllistic traversal way
simplifyStatesAndMixTs :: forall p. (Eq p, Hashable p)
  => Array Int (Either Bool Int)
  -> Array Int (MTerm.Term p Int Int)
  -> Array Int Int
  -> Int
  -> Either Bool (Array Int (MTerm.Term p Int Int), Array Int Int, Int)
simplifyStatesAndMixTs ixMap mterms states init = case sequence states1 of
  Right states' -> Right (mterms, states', init)
  Left _ -> states1!init >> simplifyStatesAndMixTs ixMap2 mterms2 states2 init2
  where
  states1 = fmap (ixMap!) states

  getQs = (`appEndo` []) . getConst .
    MTerm.modChilds MTerm.pureChildMod{ MTerm.lQ = Const . Endo . (:) }
  parented = accumArray (\_ _ -> True) False (bounds states)$
    (init, ()) : map (, ()) (concatMap getQs$ elems mterms)
  (lefts, rights) = partition (isLeft . snd)$
    zipWith noparentLeft [0..] (elems states1)
    where noparentLeft i x = if parented!i then (i, x) else (i, Left False)

  lefts' = lefts <&> \case (i, Left x) -> (i, x)
  rights' = rights <&> \case (i, Right x) -> (i, x)

  groups = groupWith snd$ sortWith snd rights'  -- PERF: use hashmap? radix grouping?
  states2 = listArray'$ snd . head <$> groups
  oldToNew = concat$ zipWith (\i' xs -> map ((, i') . fst) xs) [0..] groups

  qMap :: Array Int (Either Bool Int)
  qMap = array (bounds states)$ map (second Left) lefts' ++ map (second Right) oldToNew

  init2 = qMap!init & \case Right x -> x

  (ixMap2, listArray' -> mterms2) = runST action where
    action :: forall s. ST s (Array Int (Either Bool Int), [MTerm.Term p Int Int])
    action = runHashConsT$
      fmap (fmap fst) <$> cataScanT' @(LSTArray s) traversed alg mterms

  alg t = case MTerm.modChilds MTerm.pureChildMod{ MTerm.lQ = (qMap!) } t of
    Left b -> return$ Left b
    Right t -> case MTerm.simplify (getCompose . unFix . snd) fst t of
      Left b -> return$ Left b
      Right (Left it) -> return$ Right it
      Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)


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
    | cost mterms1 > cost mterms3 = closure ixMap3 bterms2 mterms3
    | otherwise = (ixMap1, bterms1, mterms1)
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

  mhylogebra (g, i) = return
    (runIdentity$ modPT (return . (g,)) (return . (g,)) (mterms!i), alg g)

  alg (Any False) _ = return$ error "accessing element without parents"
  alg _ t = case modPT id pure t of
    Left b -> return$ Left b
    Right t -> case MTerm.simplify (getCompose . unFix . snd) fst t of
      Left b -> return$ Left b
      Right (Left it) -> return$ Right it
      Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)

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


-- TODO the trees are traversed thrice, we need a setter generator for trees
unswallow :: forall p. BoolAfaSwallowed p -> BoolAfaUnswallowed p
unswallow BoolAfa{boolTerms=bterms, afa=afa@Afa{terms=mterms, states=transitions}} =
  runST action where
  action :: forall s. ST s (BoolAfaUnswallowed p)
  action = do
    ((transitions', mterms'), bterms') <- runNoConsT$ do
      bgs <- newArray @(LSTArray s) (bounds bterms) mempty
      runNoConsT$ do
        mgs <- newArray @(LLSTArray s) (bounds mterms) mempty
        trs <- for transitions$ mhylogebra (Any True) 
        let Enclosing before after = traverseOf (traversed . _1)
              (msetter mgs bgs arrayEncloser') trs
        before
        ixMaps <- traverseOf _2 unsafeFreeze =<< hyloScanT00'
          (lift$ unsafeFreeze =<< hyloScanTTerminal' traversed bhylogebra bgs)
          (,)
          (msetter mgs bgs arrayEncloser)
          (\(g, i) -> mhylogebra g (mterms!i))
          mgs
        runReaderT after ixMaps >>= traverse (\(t, alg) -> alg t)

    return$ BoolAfa (listArray' bterms')
      afa{ terms = listArray' mterms', states = transitions'}

  ifG (Any True) x = x
  ifG _ _ = return$ error "accessing element without parents"

  untree t = cataT (treeTraversal traversed) (either return nocons) t
  bhylogebra (g, i) = return ((g,) <$> bterms!i, ifG g untree)

  modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }
  msetter mgs bgs mEncloser = flip treeModChilds (mEncloser mgs fst)$
    modPT$ traverseOf traversed (arrayEncloser' (LiftArray bgs) snd)
  mhylogebra g t = return
    ( runIdentity$ treeModChilds (modPT$ return . ((g,) <$>)) (return . (g,)) t
    , ifG g$ cataT (treeTraversal$ modPT$ lift . untree) (either return nocons)
    )


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
  alg 1 t = return$ Node t
  alg _ tb = Leaf<$> nocons (Node tb)

  modPT lP lT = MTerm.modChilds MTerm.pureChildMod{ MTerm.lT = lT, MTerm.lP = lP }

  bhylogebra (g, i) = return ((g,) <$> bterms!i, alg g)
  mhylogebra (g, i) = return
    (runIdentity$ modPT (return . (g,)) (return . (g,)) (mterms!i), alg g)
