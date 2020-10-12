{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DeriveAnyClass #-}

module Afa.Convert.Separated
  ( separate
  , alg
  , QTerm(..)
  , ATerm(..)
  , DisjunctItem(..)
  , SeparatedFormula(..)
  , SeparatedAfa(..)
  )
  where

import Control.Arrow ((***), (&&&))
import Data.List (group, sort, find)
import Data.Functor.Compose
import Data.Monoid
import Control.Monad.State.Lazy
import Control.Monad.Writer
import Data.Array.Unsafe
import Data.Array
import Control.Monad.ST
import Data.Hashable
import Data.Hashable.Lifted
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import Control.Lens.Prism

import Control.Monad
import GHC.Generics
import Data.Functor.Classes
import qualified Data.List
import Data.Functor.Foldable
import Generic.Data (Generically1(..))
import Generic.Data.Orphans ()
import Data.Functor.Foldable.Dag.Monadic (cataScanM)
import Data.Functor.Tree
import Data.Functor.Foldable.Dag.TreeNested (condenseTreesInDag, Swallow(..))
import Data.Functor.Foldable.Dag.Consing (hashCons', runHashConsMonadT, HashConsMonadT)
import qualified Data.Functor.Foldable.Dag.TreeNested as TreeDag

import Afa
import Afa.Term
import Afa.Ops.Preprocess (sortUniq, toArr, getExtPtrMask)
import qualified Afa.Term.Prism as Afa.Prism
import Afa.Term.Prism.Ops.Simplify (positiveSimplify_alg, nolitSimplify_alg)

data QTerm rec
  = QState Int
  | QOr [rec]
  | QAnd [rec]
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1, Hashable, Hashable1)
  deriving Eq1 via (Generically1 QTerm)
  deriving Show1 via (Generically1 QTerm)

instance Afa.Prism.PositiveTerm QTerm where
  or = prism QOr$ \case QOr a -> Right a; x -> Left x
  and = prism QAnd$ \case QAnd a -> Right a; x -> Left x

data ATerm rec
  = AVar Int
  | ANot rec
  | AOr [rec]
  | AAnd [rec]
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1, Hashable, Hashable1)
  deriving Eq1 via (Generically1 ATerm)
  deriving Show1 via (Generically1 ATerm)

instance Afa.Prism.PositiveTerm ATerm where
  or = prism AOr$ \case AOr a -> Right a; x -> Left x
  and = prism AAnd$ \case AAnd a -> Right a; x -> Left x

instance Afa.Prism.Term ATerm where
  not = prism ANot$ \case ANot a -> Right a; x -> Left x

data DisjunctItem qterm aterm
  = QItem qterm
  | AItem aterm
  | Conjunct qterm aterm
  deriving (Show, Eq, Ord)

data SeparatedFormula qterm aterm
  = STrue
  | SFalse
  | QPure qterm
  | APure aterm
  | Disjunct [DisjunctItem qterm aterm]
  deriving (Show, Eq)

data Partition qterm aterm = Partition
  { hasTrue :: Bool
  , hasFalse :: Bool
  , qpures :: [qterm]
  , apures :: [aterm]
  , disjuncts :: [[DisjunctItem qterm aterm]]
  }

lsortUniq :: (Eq a, Ord a) => [a] -> [a]
lsortUniq = map head . group . sort

uniqDisjunct
  :: (Eq qterm, Eq aterm, Ord qterm, Ord aterm)
  => [DisjunctItem qterm aterm] -> SeparatedFormula qterm aterm
uniqDisjunct items = Disjunct$ lsortUniq items

partition :: [SeparatedFormula qterm aterm] -> Partition qterm aterm
partition = foldr go (Partition False False [] [] []) where
  go STrue p = p{hasTrue = True}
  go SFalse p = p{hasFalse = True}
  go (QPure t) p@Partition{qpures} = p{qpures = t : qpures}
  go (APure t) p@Partition{apures} = p{apures = t : apures}
  go (Disjunct t) p@Partition{disjuncts} = p{disjuncts = t : disjuncts}

partitionDisjuncts :: [DisjunctItem qterm aterm] -> ([qterm], [aterm], [(qterm, aterm)])
partitionDisjuncts = foldr go ([], [], []) where
  go (QItem q) (qs, as, qas) = (q:qs, as, qas)
  go (AItem a) (qs, as, qas) = (qs, a:as, qas)
  go (Conjunct q a) (qs, as, qas) = (qs, as, (q, a):qas)

alg
  :: forall m qref aref. (Monad m)
  => ([DisjunctItem qref aref] -> SeparatedFormula qref aref)
  -> (QTerm qref -> m qref)
  -> (ATerm aref -> m aref)
  -> Term (SeparatedFormula qref aref)
  -> m (SeparatedFormula qref aref)
alg disjunct newQ newA = \case
  LTrue -> return STrue
  LFalse -> return SFalse
  Var i -> APure <$> newA (AVar i)
  State i -> QPure <$> newQ (QState i)
  Not STrue -> return SFalse
  Not SFalse -> return STrue
  Not (APure t) -> APure <$> newA (ANot t)
  Not _ -> error "negation above states"
  Or ts ->
    let
      Partition{hasTrue, qpures, apures, disjuncts} = partition ts
      qpure = case qpures of [x] -> return x; _ -> newQ$ QOr qpures
      apure = case apures of [x] -> return x; _ -> newA$ AOr apures
    in
    case () of
      _ | hasTrue -> return STrue
        | otherwise -> case (null qpures, null apures, null disjuncts) of
            (True, True, True) -> return SFalse
            (False, True, True) -> QPure <$> qpure
            (True, False, True) -> APure <$> apure
            _ -> disjunct <$> do
              addQ <- if null qpures then return id else (:) . QItem <$> qpure
              addA <- if null apures then return id else (:) . AItem <$> apure
              return$ addQ$ addA$ concat disjuncts

  And ts ->
    let
      Partition{hasFalse, qpures, apures, disjuncts} = partition ts
      (singletons, disjuncts') =
        Data.List.partition (\case (_:_:_) -> False; (_:_) -> True) disjuncts

      qpure = case qpures of [x] -> return x; _ -> newQ$ QAnd qpures
      apure = case apures of [x] -> return x; _ -> newA$ AAnd apures

      qpures' = qpures ++ map ((\case (Conjunct q _) -> q) . head) singletons
      apures' = apures ++ map ((\case (Conjunct _ a) -> a) . head) singletons

      qpure' = case qpures' of [x] -> return x; _ -> newQ$ QAnd qpures'
      apure' = case apures' of [x] -> return x; _ -> newA$ AAnd apures'

      cartesian_product = sequence disjuncts'
    in
    case () of
      _ | hasFalse -> return SFalse
        | otherwise -> case (null qpures, null apures, null disjuncts) of
            (True, True, True) -> return STrue
            (False, True, True) -> QPure <$> qpure
            (True, False, True) -> APure <$> apure
            _ -> do
              addQ <- if null qpures' then return id else (:) . QItem <$> qpure'
              addA <- if null apures' then return id else (:) . AItem <$> apure'
              conjuncts <- forM cartesian_product$ simpleAnd . addQ . addA
              simpleOr conjuncts

  where
  simpleAnd
    :: [DisjunctItem qref aref]
    -> m (DisjunctItem qref aref)
  simpleAnd parts = do
    qs <- createTerm (newQ . QAnd)$ qs1 ++ qs2
    as <- createTerm (newA . AAnd)$ as1 ++ as2
    return$ case (qs, as) of
      (Just q, Just a) -> Conjunct q a
      (Just q, Nothing) -> QItem q
      (Nothing, Just a) -> AItem a
    where
    (qs1, as1, unzip -> (qs2, as2)) = partitionDisjuncts parts

  createTerm :: ([a] -> m a) -> [a] -> m (Maybe a)
  createTerm joiner = \case
    [] -> return Nothing
    [x] -> return$ Just x
    xs -> Just <$> joiner xs

  simpleOr
    :: [DisjunctItem qref aref]
    -> m (SeparatedFormula qref aref)
  simpleOr parts = do
    qs' <- createTerm (newQ . QAnd) qs
    as' <- createTerm (newA . AAnd) as
    return$ case (qs', as') of
      (Just q, Just a) ->  disjunct$ QItem q : AItem a : qas
      (Just q, Nothing) ->  disjunct$ QItem q : qas
      (Nothing, Just a) ->  disjunct$ AItem a : qas
      (Nothing, Nothing) -> disjunct qas
    where
    (qs, as, map (uncurry Conjunct) -> qas) = partitionDisjuncts parts

data SeparatedAfa = SeparatedAfa
  { qterms :: Array Int (TreeF QTerm Int)
  , aterms :: Array Int (TreeF ATerm Int)
  , states :: Array Int [(Int, Int)]  -- ^ -1 means True
  }
  deriving (Show, Eq)

separate :: Afa -> SeparatedAfa
separate afa@Afa{Afa.states, terms} = SeparatedAfa
  { qterms = qterms4
  , aterms = aterms4
  , states = fmap (lsortUniq . map (mapPtr qMap4 *** mapPtr aMap4)) states'
  }
  where
  termMap :: Array Int (SeparatedFormula Int Int)
  ((termMap, toArr -> qterms), toArr -> aterms) = runST$ runSeparateT$
    cataScanM (treeFAlgM$ alg uniqDisjunct newQ newA) terms
    >>= lift . unsafeFreeze

  states' = fmap point states
  (qptrs, aptrs) = filter (/= -1) *** filter (/= -1)$ unzip$ concat$ elems states'

  qextPtrMask = getExtPtrMask qterms qptrs
  aextPtrMask = getExtPtrMask aterms aptrs

  qswallow :: Int -> Int -> TreeF QTerm Int -> Swallow
  qswallow ix parentCount t
    | Afa.Prism.positiveIsRecursive (project t) =
        if parentCount > 1 || qextPtrMask!ix then Keep else Swallow
    | otherwise = if qextPtrMask!ix then Copy else Swallow

  aswallow :: Int -> Int -> TreeF ATerm Int -> Swallow
  aswallow ix parentCount t
    | Afa.Prism.isRecursive (project t) =
        if parentCount > 1 || aextPtrMask!ix then Keep else Swallow
    | otherwise = if aextPtrMask!ix then Copy else Swallow

  (qMap, qterms2) = condenseTreesInDag qswallow qterms
  (aMap, aterms2) = condenseTreesInDag aswallow aterms

  qterms3 = cata positiveSimplify_alg <$> qterms2
  aterms3 = cata nolitSimplify_alg <$> aterms2

  qptrs3 = map (qMap!) qptrs
  aptrs3 = map (aMap!) aptrs

  simplify
    :: ( (Array Int (TreeF QTerm Int), [Int], Array Int Int)
       , (Array Int (TreeF ATerm Int), [Int], Array Int Int)
       )
    -> ( (Array Int (TreeF QTerm Int), [Int], Array Int Int)
       , (Array Int (TreeF ATerm Int), [Int], Array Int Int)
       )
  simplify ((qterms, qptrs, qMap), (aterms, aptrs, aMap)) =
    ((qterms'', qptrs', qMap'), (aterms'', aptrs', aMap'))
    where
    (qterms', qptrs', qMap') =
      hashConsThenSwallow (Afa.Prism.positiveIsRecursive . project) qterms qptrs qMap
    (aterms', aptrs', aMap') =
      hashConsThenSwallow (Afa.Prism.isRecursive . project) aterms aptrs aMap

    qterms'' = cata positiveSimplify_alg <$> qterms'
    aterms'' = cata nolitSimplify_alg <$> aterms'

  iters = map (cost &&& id)$ iterate simplify
    ((qterms3, qptrs3, qMap), (aterms3, aptrs3, aMap))

  cost ((qterms, _, _), (aterms, _, _)) = (TreeDag.cost qterms, TreeDag.cost aterms)

  Just ((_, ((qterms4, _, qMap4), (aterms4, _, aMap4))), _) =
    find (\(((qc1, ac1), _), ((qc2, ac2), _)) -> qc1 <= qc2 && ac1 <= ac2)
    $ zip iters (tail iters)

  mapPtr m = \case -1 -> -1; i -> m!i

  point :: Int -> [(Int, Int)]
  point ix = case termMap!ix of
    STrue -> [(-1, -1)]
    SFalse -> []
    QPure qix -> [(qix, -1)]
    APure aix -> [(-1, aix)]
    Disjunct xs -> flip map xs$ \case
      QItem qix -> (qix, -1)
      AItem aix -> (-1, aix)
      Conjunct qix aix -> (qix, aix)

hashConsThenSwallow
  :: (Traversable f, Eq (f Int), Hashable (f Int), Afa.Prism.PositiveTerm f)
  => (TreeF f Int -> Bool)
  -> Array Int (TreeF f Int)
  -> [Int]
  -> Array Int Int
  -> (Array Int (TreeF f Int), [Int], Array Int Int)
hashConsThenSwallow isRecursive terms extPtrs ixMap0 = (terms2, extPtrs'', ixMap0')
  where
  (ixMap1, toArr -> terms1) = runST$ runHashConsMonadT$
    cataScanM (treeFAlgM$ hashCons' . sortUniq) terms >>= lift . unsafeFreeze

  extPtrs' = map (ixMap1!) extPtrs
  extPtrMask = getExtPtrMask terms1 extPtrs'

  swallow ix parentCount t
    | isRecursive t = if parentCount > 1 || extPtrMask!ix then Keep else Swallow
    | otherwise = if extPtrMask!ix then Copy else Swallow

  (ixMap2, terms2) = condenseTreesInDag swallow terms1
  extPtrs'' = map (ixMap2!) extPtrs'
  ixMap0' = fmap ((ixMap2!) . (ixMap1!)) ixMap0

newtype SeparateT m a = SeparateT
  (HashConsMonadT (QTerm Int) (QTerm Int)
    (HashConsMonadT (ATerm Int) (ATerm Int) m) a)
  deriving newtype (Functor, Applicative, Monad)

newQ :: Monad m => QTerm Int -> SeparateT m Int
newQ = SeparateT . hashCons' . sortUniq

newA :: Monad m => ATerm Int -> SeparateT m Int
newA = SeparateT . lift . hashCons' . sortUniq

instance MonadTrans SeparateT where
  lift = SeparateT . lift . lift

runSeparateT :: Monad m => SeparateT m a -> m ((a, [QTerm Int]), [ATerm Int])
runSeparateT (SeparateT action) = runHashConsMonadT$ runHashConsMonadT action
