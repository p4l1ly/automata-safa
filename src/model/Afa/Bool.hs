{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module Afa.Bool where

import Data.Either
import Data.Maybe
import Control.Arrow
import Data.Traversable
import Control.Monad.Reader
import Data.Array
import Data.Array.ST
import Data.Array.Unsafe
import Data.Monoid (Any(..), Sum(..))
import Control.RecursionSchemes.Lens
import Control.Lens
import Control.Monad.ST
import Data.Fix
import Data.Functor.Compose
import Data.Hashable

import Afa
import qualified Afa.Term.Mix as MixT
import qualified Afa.Term.Bool as BoolT
import qualified Afa.Term.Bool.Simplify as BoolTSimplify
import Afa.Lib.Tree
import Afa.Lib.LiftArray
import Afa.Lib (listArray', (>&>))


data BoolAfa boolTerms afa = BoolAfa
  { boolTerms :: boolTerms
  , afa :: afa
  }


type BoolTermITree p = Tree (BoolT.Term p) Int
type BoolAfaSwallowed p = BoolAfa
  (Array Int (BoolTermITree p))
  (AfaSwallowed (BoolTermITree p))
type BoolAfaUnswallowed p = BoolAfa
  (Array Int (BoolT.Term p Int))
  (AfaUnswallowed Int)


simplifyBoolTs :: forall p. (Eq p, Hashable p)
  => Array Int Any
  -> (Array Int (Either Bool Int), Array Int (BoolT.Term p Int))
  -> (Array Int (Either Bool Int), Array Int (BoolT.Term p Int))
simplifyBoolTs gs (ixMap, arr) = runST action where
  action :: forall s. ST s (Array Int (Either Bool Int), Array Int (BoolT.Term p Int))
  action = do
    (gs'M :: STArray s Int Any) <- unsafeThaw gs'
    (LiftArray ixMap'M, tList) <- runHashConsT$
      hyloScanTTerminal' traversed hylogebra (LiftArray gs'M)
    ixMap' <- unsafeFreeze ixMap'M
    return (fmap (>>= (ixMap'!) >&> fst) ixMap, listArray' tList)

  gs' = accumArray (\_ x -> x) mempty (bounds arr)
    [(i, Any True) | ((ixMap!) -> Right i, Any True) <- assocs gs]

  alg (Any False) _ = return$ error "accessing element without parents"
  alg _ t = case BoolTSimplify.simplify (getCompose . unFix . snd) fst t of
    Left b -> return$ Left b
    Right (Left it) -> return$ Right it
    Right (Right t) -> Right . (, Fix$ Compose t) <$> hashCons' (fmap fst t)

  hylogebra (g, i) = return ((g,) <$> arr!i, alg g)


simplifyBoolTsUntilFixpoint :: forall p. (Eq p, Hashable p)
  => Array Int Any
  -> Array Int (BoolT.Term p Int)
  -> (Array Int (Either Bool Int), Array Int (BoolT.Term p Int))
simplifyBoolTsUntilFixpoint gs arr = fromJust$ msum$ zipWith better iters (tail iters)
  where
  ixMap = listArray (bounds gs)$ map Right [0..]
  cost ts = (length ts, sum$ fmap length ts)
  iters = iterate
    ((cost . snd &&& id) . simplifyBoolTs gs . snd)
    (cost arr, (ixMap, arr))
  better (c1, r) (c2, _) = r <$ guard (c1 > c2)


-- to be able to cons them with boolterms
separateStatelessBottoms :: forall p. (Eq p, Hashable p)
  => BoolAfaUnswallowed p -> BoolAfaUnswallowed p
separateStatelessBottoms (BoolAfa bterms afa@Afa{terms=mterms, states=states}) =
  runST action where
  action :: forall s. ST s (BoolAfaUnswallowed p)
  action = do
    ((LiftArray (LiftArray ixMapM), mList), bList) <-
      runHashConsT$ do
        LiftArray bixMapM <- ($bterms)$ traverseOf (cataScanT traversed) hashCons'
        bixMap <- lift$ unsafeFreeze (bixMapM :: STArray s Int Int)
        runNoConsT$
          ($mterms)$ traverseOf (cataScanT traversed)$ \case
            MixT.State q -> (Nothing,) <$> nocons (MixT.State q)
            MixT.Predicate b -> (Just b,) <$> nocons (MixT.Predicate (bixMap!b))
            MixT.LTrue -> handleStateless BoolT.LTrue
            MixT.And bts -> case mapM fst bts of
              Nothing -> (Nothing,) <$> nocons (MixT.And$ snd <$> bts)
              Just bs -> handleStateless$ BoolT.And bs
            MixT.Or bts -> case mapM fst bts of
              Nothing -> (Nothing,) <$> nocons (MixT.Or$ snd <$> bts)
              Just bs -> handleStateless$ BoolT.Or bs

    ixMap <- unsafeFreeze (ixMapM :: STArray s Int (Maybe Int, Int))
    return$ BoolAfa
      (listArray'$ elems bterms ++ bList)
      afa{ terms = listArray' mList, states = fmap (snd . (ixMap!)) states }

  handleStateless bt = do
    ref <- lift$ hashCons' bt
    fmap (Just ref,)$ nocons$ MixT.Predicate ref


-- to be able to flatten them with mixterms
separatePositiveTops :: forall p q. (Eq q, Hashable q)
  => Array Int (BoolT.Term p Int)
  -> Array Int (MixT.Term Int q Int)
  -> (Array Int Int, Array Int (BoolT.Term p Int), Array Int (MixT.Term Int q Int))
separatePositiveTops bterms mterms =
  runST action where
  action :: forall s. ST s
    (Array Int Int, Array Int (BoolT.Term p Int), Array Int (MixT.Term Int q Int))
  action = do
    bgs <- LiftArray . LiftArray <$> newArray @(STArray s) (bounds mterms) mempty

    ((LiftArray (LiftArray ixMapM), mList), bList) <- runNoConsT$ runHashConsT$ do
      bixMap <- unsafeFreeze =<< hyloScanTTerminal' traversed bhylogebra bgs
      ($mterms)$ traverseOf (cataScanT traversed)$ \case
        MixT.Predicate p -> case bixMap!p of
          Right p' -> hashCons'$ MixT.Predicate p'
          Left t -> return t
        x -> hashCons' x

    ixMap <- unsafeFreeze (ixMapM :: STArray s Int Int)
    return (ixMap, listArray' bList, listArray' mList)

  bhylogebra (g, i) = return
    ( (g',) <$> bterm
    , case g' of
        Any True -> fmap Right . lift . nocons .
          fmap (fromLeft$ error "positive under negative")
        Any False -> \case
          BoolT.LTrue -> Left <$> hashCons' MixT.LTrue
          BoolT.And ixs -> fmap Left$ do
            ixs' <- forM ixs$ either (hashCons' . MixT.Predicate) return
            hashCons'$ MixT.And ixs'
          BoolT.Or ixs -> fmap Left$ do
            ixs' <- forM ixs$ either (hashCons' . MixT.Predicate) return
            hashCons'$ MixT.Or ixs'
          _ -> error "cannot be positive"
    )
    where
    bterm = bterms!i
    g' = case bterm of
      BoolT.Not _ -> Any True
      BoolT.LFalse -> Any True
      BoolT.Predicate _ -> Any True
      _ -> g


unswallow :: forall p. BoolAfaSwallowed p -> BoolAfaUnswallowed p
unswallow BoolAfa{boolTerms=bterms, afa=afa@Afa{terms=mterms, states=transitions}} =
  runST action where
  action :: forall s. ST s (BoolAfaUnswallowed p)
  action = do
    mgs <- LiftArray . LiftArray <$> newArray @(STArray s) (bounds mterms) mempty
    bgs <- LiftArray <$> newArray @(STArray s) (bounds bterms) mempty

    ((transitions', mterms'), bterms') <- runNoConsT$ runNoConsT$ do
      trs <- for transitions$ mhylogebra (Any True) 
      let Enclosing before after = traverseOf (traversed . _1)
            (msetter mgs bgs arrayEncloser') trs
      before
      ixMaps <- traverseOf _2 unsafeFreeze =<< hyloScanT00'
        (lift$ hyloScanTTerminal' traversed bhylogebra bgs >>= unsafeFreeze)
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

  modPT lP lT = MixT.modChilds MixT.pureChildMod{ MixT.lT = lT, MixT.lP = lP }
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
    mgs <- LiftArray . LiftArray <$> newArray @(STArray s) (bounds mterms) mempty
    bgs <- LiftArray <$> newArray @(STArray s) (bounds bterms) mempty

    ((transitions', mterms'), bterms') <- runNoConsT$ runNoConsT$ do
      let Enclosing before after = for transitions$ arrayEncloser' mgs id . (Sum 1,)
      before
      ixMaps <- unsafeFreeze . snd =<< hyloScanT00'
        (lift$ hyloScanTTerminal' traversed bhylogebra bgs >>= unsafeFreeze)
        (,)
        (modPT (arrayEncloser' (LiftArray bgs) snd) (arrayEncloser mgs fst))
        (\(g, i) -> mhylogebra g (mterms!i))
        mgs
      runReaderT after ixMaps

    return$ BoolAfa (listArray' bterms')
      afa{ terms = listArray' mterms', states = transitions'}

  alg 0 _ = return$ error "accessing element without parents"
  alg 1 t = return$ Node t
  alg _ tb = Leaf<$> nocons (Node tb)

  modPT lP lT = MixT.modChilds MixT.pureChildMod{ MixT.lT = lT, MixT.lP = lP }

  bhylogebra (g, i) = return ((g,) <$> bterms!i, alg g)
  mhylogebra g t = return (runIdentity$ modPT (return . (g,)) (return . (g,)) t, alg g)
