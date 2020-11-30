{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Afa.Bool where

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
  -> Array Int (Either Bool Int)
  -> Array Int (BoolT.Term p Int)
  -> (Array Int (Either Bool Int), Array Int (BoolT.Term p Int))
simplifyBoolTs gs ixMap arr = runST action where
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


swallowBoolTs :: forall p. (Eq p, Hashable p)
  => Array Int (Sum Int)
  -> Array Int (Either Bool Int)
  -> Array Int (BoolT.Term p Int)
  -> ( Array Int (Either Bool (Tree (BoolT.Term p) Int))
     , Array Int (Tree (BoolT.Term p) Int)
     )
swallowBoolTs gs ixMap arr = runST action where
  action :: forall s. ST s
    ( Array Int (Either Bool (Tree (BoolT.Term p) Int))
    , Array Int (Tree (BoolT.Term p) Int)
    )
  action = do
    (gs'M :: STArray s Int (Sum Int)) <- unsafeThaw gs'
    (LiftArray ixMap'M, tList) <- runNoConsT$
      hyloScanTTerminal' traversed hylogebra (LiftArray gs'M)
    ixMap' <- unsafeFreeze ixMap'M
    return (fmap (fmap (ixMap'!)) ixMap, listArray' tList)

  gs' = accumArray (\_ x -> x) mempty (bounds arr)
    [ (i, parentCount)
    | ((ixMap!) -> Right i, parentCount) <- assocs gs
    , parentCount > 0
    ]

  alg 0 _ = return$ error "accessing element without parents"
  alg 1 t = return$ Node t
  alg _ tb = Leaf<$> nocons (Node tb)

  hylogebra (g, i) = return ((g,) <$> arr!i, alg g)


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

    return BoolAfa
      { boolTerms = listArray' bterms'
      , afa = afa
          { terms = listArray' mterms'
          , states = transitions'
          }
      }

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

    return BoolAfa
      { boolTerms = listArray' bterms'
      , afa = afa
          { terms = listArray' mterms'
          , states = transitions'
          }
      }

  alg 0 _ = return$ error "accessing element without parents"
  alg 1 t = return$ Node t
  alg _ tb = Leaf<$> nocons (Node tb)

  modPT lP lT = MixT.modChilds MixT.pureChildMod{ MixT.lT = lT, MixT.lP = lP }

  bhylogebra (g, i) = return ((g,) <$> bterms!i, alg g)
  mhylogebra g t = return (runIdentity$ modPT (return . (g,)) (return . (g,)) t, alg g)
