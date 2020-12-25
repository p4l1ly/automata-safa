{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}

module Afa.Ops.Goblin where

import Debug.Trace

import Data.Traversable
import Data.Array.ST
import Data.Array.Unsafe
import Data.Functor
import Control.Monad
import Data.Array
import Control.Monad.ST
import Control.Lens
import Control.Monad.Trans
import Control.RecursionSchemes.Lens
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Void
import Data.Maybe

import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import Afa
import Afa.Term.Mix
import Afa.Term.Mix.Simplify (deUnary)

-- split
--   :: Term p q (Maybe tq, ta)
--   -> Either (Term Void q tq, [ta]) (Term p tq ta)
-- split LTrue = Left (LTrue, [])
-- split (State q) = Left (State q, [])
-- split (Predicate p) = Right (Predicate p)
-- split (Or ts) = case sequence tqs of
--   Just ts' -> Left (Or ts', [])
--   _ -> Right$ Or tas
--   where (tqs, tas) = NE.unzip ts
-- split (And ts) = case mapM fst ts of
--   Just ts' -> Left (And ts', [])
--   _ | null tqs -> Right$ And$ NE.map snd ts
--     | otherwise -> Left (And$ NE.fromList tqs, tas)
--   where
--   (map (fromJust . fst) -> tqs, map snd -> tas) = NE.partition (isJust . fst) ts
-- 
-- split'
--   :: (Show p, Monad m)
--   => (Bool, Term p Int (Maybe (Int, Bool), Int))
--   -> NoConsT (Term Void Int (Int, Bool))
--        (NoConsT (Term p (Int, Bool) Int) m)
--        (Maybe (Int, Bool), Int)
-- split' (False, Or xs) = (Nothing,) <$> lift (nocons$ Or$ fmap snd xs)
-- split' (_, x) =
--   case split x of
--     Left (State ((, False) -> q), []) -> (Just q,) <$> lift (nocons$ State q)
--     Left (State _, _) -> error "state with adep arguments"
--     Left (tq, tas) -> do
--       q <- case deUnary tq of
--         Left q -> return q
--         Right tq -> (, True) <$> nocons tq
--       a <- lift$ nocons$ State q
--       if null tas
--         then return (Just q, a)
--         else (Just q,) <$> lift (nocons$ And$ a :| tas)
--     Right ta -> (Nothing,) <$> lift (nocons ta)
-- 
-- isGate (Or _) = True
-- isGate (And _) = True
-- isGate _ = False
-- 
-- -- FIXME!!!! resolve cycles, e.g. Q0 -> q0 & q1
-- goblin :: forall p. Show p => AfaUnswallowed p -> Maybe (AfaUnswallowed p)
-- goblin afa@Afa{terms, states} = guard (any isGate qdep) $> afa
--   { terms = listArray'$ adep' ++ qdep'
--   , states = listArray'$ elems states' ++ zipWith const [adepL ..] qdep
--   }
--   where
--   purities = terms & cataScan traversed %~ \case
--     Predicate _ -> False
--     x -> and x
-- 
--   termsWithPurities = listArray (bounds terms)$ zip (elems purities) (elems terms)
-- 
--   ((ixMap, traceShowId -> qdep), adep) = runST action where
--     action :: forall s. ST s
--       ( (Array Int (Maybe (Int, Bool), Int)
--         , [Term Void Int (Int, Bool)]
--         )
--       , [Term p (Int, Bool) Int]
--       )
--     action = runNoConsT$ runNoConsT$
--       cataScanT' @(LLSTArray s) (_2 . traversed) split' termsWithPurities
-- 
--   stateL = rangeSize$ bounds states
--   adepL = length adep
--   adep' = adep <&> runIdentity . modChilds pureChildMod {lQ = shiftState}
--   qdep' = qdep <&> runIdentity . modChilds pureChildMod {lP = absurd, lT = shiftQDep}
-- 
--   shiftState (i, new) = Identity$ if new then i + stateL else i
--   shiftQDep (i, new) = Identity$ if new then i + adepL else snd$ ixMap!(states!i)
-- 
--   states' = fmap (snd . (ixMap!)) states
-- 
-- goblinUntilFixpoint :: forall p. Show p => AfaUnswallowed p -> AfaUnswallowed p
-- goblinUntilFixpoint (traceShowId -> afa) = maybe afa goblinUntilFixpoint$ goblin afa


data BackEdgeMark p
  = Unvisited
  | Recur
  | Recurring
  | Evaluated (Term p (Bool, Int) (Bool, Int))

instance Semigroup (BackEdgeMark p) where
  Unvisited <> x = x
  x <> _ = x

markBack :: forall p. AfaUnswallowed p -> Array Int (Term p (Bool, Int) (Bool, Int))
markBack (Afa terms states init) = runST getMarks <&> \case Evaluated x -> x
  where
  getMarks :: forall s. ST s (Array Int (BackEdgeMark p))
  getMarks = do
    marks <- newArray @(STArray s) (bounds terms) Unvisited
    writeArray marks (states!init) Recur
    dfs (traversal marks) marks (states!init)
    unsafeFreeze marks

  traversal :: STArray s Int (BackEdgeMark p)
    -> LensLike (ST s) (BackEdgeMark p, Int) Bool (BackEdgeMark p, Int) Bool
  traversal arr rec (x, i) = case x of
    Recur -> do
      writeArray arr i Recurring 
      term' <- terms!i & modChilds pureChildMod
        { lQ = \q -> (, q) <$> rec (Recur, states!q)
        , lT = \j -> (, j) <$> rec (Recur, j)
        }
      writeArray arr i (Evaluated term')
      return False
    Recurring -> return True
    Evaluated _ -> return False
    Unvisited -> error "visiting unvisited"

newState :: Monad m => Int -> NoConsT Int m Int
newState = nocons

newCombined :: (MonadTrans mt2, Monad (mt (NoConsT x m)), MonadTrans mt, Monad m)
  => x -> mt2 (mt (NoConsT x m)) Int
newCombined = lift . lift . nocons

newQDep :: (MonadTrans mt, Monad m) => x -> mt (NoConsT x m) Int
newQDep = lift . nocons

qac
  :: Monad m
  => Term p (Bool, Int) (Bool, (Maybe (Bool, Either (Bool, Int) Int, Int), Maybe Int, Int))
  -> NoConsT Int
       ( NoConsT (Term Void Void (Bool, Either (Bool, Int) Int))
           (NoConsT (Term p (Bool, Int) (Bool, Int)) m)
       )
       (Maybe (Bool, Either (Bool, Int) Int, Int), Maybe Int, Int)
qac LTrue = do
  c <- newCombined LTrue
  q <- newQDep LTrue
  return (Just (False, Right q, c), Nothing, c)
qac (Predicate p) = do
  c <- newCombined$ Predicate p
  return (Nothing, Just c, c)
qac (State bq@(back, q)) = do
  c <- newCombined$ State bq
  return (Just (back, Left (back, q), c), Nothing, c)
qac (Or ts)
  | not$ null as = do
      c <- newCombined$ Or$ fmap (\(b, (_, _, t)) -> (b, t)) ts
      return (Nothing, Just c, c)
  | all fst qs = do
      c <- newCombined$ Or$ fmap (\(b, (_, _, t)) -> (b, t)) ts
      q <- newQDep$ Or$ NE.fromList qs0
      return (Just (True, Right q, c), Nothing, c)
  | otherwise = do
      q <- newQDep$ Or$ NE.fromList qs0
      s <- newState q
      c <- newCombined$ State (False, s)
      return (Just (False, Right q, c), Nothing, c)
  where
  lts = NE.toList ts
  qsBoth = mapMaybe (\(b, (q, _, _)) -> (b,) <$> q) lts
  qs0 = map (\(b, (_, q, _)) -> (b, q)) qsBoth
  qs = map (\(b, (qb, q, _)) -> (b || qb, q)) qsBoth
  as = mapMaybe (^._2._2) lts
qac (And ts)
  | null qs = do
      c <- newCombined$ And$ fmap (\(b, (_, _, t)) -> (b, t)) ts
      return (Nothing, Just c, c)
  | null as =
      if back
      then do
        c <- newCombined$ And$ fmap (\(b, (_, _, t)) -> (b, t)) ts
        q <- newQDep$ And$ NE.fromList qs0
        return (Just (True, Right q, c), Nothing, c)
      else do
        q <- newQDep$ And$ NE.fromList qs0
        s <- newState q
        c <- newCombined$ State (False, s)
        return (Just (False, Right q, c), Nothing, c)
  | otherwise = do
      a <- case as of
        [a] -> return a
        _:_:_ -> newCombined$ And$ NE.fromList$ map (False,) as
      case qsBoth of
        [(b, (qb, q, qc))] -> do
          c <- newCombined$ And$ (qb, qc) :| [(False, a)]
          return (Just (back, q, qc), Just a, c)
        _:_:_
          | back -> do
             q <- newQDep$ And$ NE.fromList qs0
             qc <- newCombined$ And$ NE.fromList qcs
             c <- newCombined$ And$ (False, qc) :| [(False, a)]
             return (Just (True, Right q, qc), Just a, c)
          | otherwise -> do
             q <- newQDep$ And$ NE.fromList qs0
             s <- newState q
             qc <- newCombined$ State (False, s)
             c <- newCombined$ And$ (False, qc) :| [(False, a)]
             return (Just (False, Right q, qc), Just a, c)
  where
  lts = NE.toList ts
  qsBoth = mapMaybe (\(b, (q, _, _)) -> (b,) <$> q) lts
  qs0 = map (\(b, (_, q, _)) -> (b, q)) qsBoth
  qs = map (\(b, (qb, q, _)) -> (b || qb, q)) qsBoth
  qcs = map (\(b, (_, _, qc)) -> (b, qc)) qsBoth
  as = mapMaybe (^._2._2) lts
  back = all fst qs


goblin2 :: forall p.
     Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int
  -> Maybe (Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int)
goblin2 (Afa terms states init) = do
  (terms', states') <- runST action
  Just$ Afa (listArray' terms') (listArray' states') init
  where
  action :: forall s. ST s (Maybe ([Term p (Bool, Int) (Bool, Int)], [Int]))
  action = do
    (((ixMap, statesL), qterms), aterms) <-
      runNoConsT$ runNoConsT$ runNoConsTFrom (succ$ snd$ bounds states)$
        cataScanT' @(LLLSTArray s) (traversed._2) qac terms

    let qshift = length aterms
    let mappedStates = states <&> \i -> ixMap!i ^._3
    let pureChildMod' = pureChildMod @Identity
    let qterms' :: [Term p (Bool, Int) (Bool, Int)]
        qterms' = ($ qterms)$ map$ runIdentity . modChilds 
          pureChildMod'
          { lP = absurd
          , lQ = absurd
          , lT = \(b, i) -> case i of
              Left (qb, q) -> return (b || qb, mappedStates!q)
              Right t -> return (b, t + qshift)
          }

    return$ case statesL of
      [] -> Nothing
      _ -> Just (aterms ++ qterms', elems mappedStates ++ map (+ qshift) statesL)
