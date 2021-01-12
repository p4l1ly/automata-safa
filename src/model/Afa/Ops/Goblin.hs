{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

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

goblinUntilFixpoint :: forall p. Show p => AfaUnswallowed p -> AfaUnswallowed p
goblinUntilFixpoint afa = afa'{terms = unmarked} where
  marked = markBack afa
  closure afa = maybe afa closure$ goblin2 afa
  afa' = closure$ afa{terms = marked}
  unmarked = terms afa' <&> runIdentity . modChilds pureChildMod
    { lQ = return . snd, lT = return . snd }

data BackEdgeMark p
  = Unvisited
  | Recur
  | Recurring
  | Evaluated (Term p (Bool, Int) (Bool, Int))
  deriving Show

instance Semigroup (BackEdgeMark p) where
  Unvisited <> x = x
  x <> _ = x

markBack :: forall p. Show p => AfaUnswallowed p
  -> Array Int (Term p (Bool, Int) (Bool, Int))
markBack afa@(Afa terms states init) = runST getMarks &
  \arr -> listArray (bounds arr) (zip [0..] (elems arr)) <&>
    \case (_, Evaluated x) -> x; (i, _) -> error$ show (i, afa)
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

data QRef = QRef
  { allBackUnderneath :: Bool
  , qref :: Either (Bool, Int) Int  -- Left points to the transition of a state
  , qcref :: Int
  , unappliedBack :: Bool
  }

data Mix
  = PureA Int
  | PureQ QRef
  | OrMix QRef Int
  | AndMix QRef Int

qac
  :: Monad m
  => Term p (Bool, Int) (Bool, (Mix, Int))
  -> NoConsT Int
       ( NoConsT (Term Void Void (Bool, Either (Bool, Int) Int))
           (NoConsT (Term p (Bool, Int) (Bool, Int)) m)
       )
       (Mix, Int)
qac LTrue = do
  c <- newCombined LTrue
  q <- newQDep LTrue
  return (PureQ (QRef False (Right q) c False), c)
qac (Predicate p) = do
  c <- newCombined$ Predicate p
  return (PureA c, c)
qac (State bq@(back, q)) = do
  c <- newCombined$ State bq
  return (PureQ (QRef back (Left (back, q)) c False), c)
qac (And ts)
  | null qs0 = do
      c <- newCombined$ And$ fmap (\(b, (_, t)) -> (b, t)) ts
      return (PureA c, c)
  | null as =
      if back
      then do
        c <- newCombined$ And$ fmap (\(b, (_, t)) -> (b, t)) ts
        q <- newQDep$ And$ NE.fromList qs0
        return (PureQ (QRef True (Right q) c False), c)
      else do
        q <- newQDep$ And$ NE.fromList qs0
        s <- newState q
        c <- newCombined$ State (False, s)
        return (PureQ (QRef False (Right q) c False), c)
  | otherwise = do
      a <- case as of
        [a] -> return a
        _:_:_ -> newCombined$ And$ NE.fromList$ map (False,) as
      case qsBoth of
        [(b, QRef _ q qc b2)] -> do
          c <- newCombined$ And$ (b || b2, qc) :| [(False, a)]
          return (AndMix (QRef back q qc (b || b2)) a, c)
        _:_:_
          | back -> do
             q <- newQDep$ And$ NE.fromList qs0
             qc <- newCombined$ And$ NE.fromList qcs
             c <- newCombined$ And$ (False, qc) :| [(False, a)]
             return (AndMix (QRef True (Right q) qc False) a, c)
          | otherwise -> do
             q <- newQDep$ And$ NE.fromList qs0
             s <- newState q
             qc <- newCombined$ State (False, s)
             c <- newCombined$ And$ (False, qc) :| [(False, a)]
             return (AndMix (QRef False (Right q) qc False) a, c)
  where
  lts = NE.toList ts
  qsBoth = flip mapMaybe lts$ \(b, fst -> mix) -> (b,) <$> case mix of
    PureQ qref -> Just qref
    AndMix qref _ -> Just qref
    _ -> Nothing
  qs0 = map (\(b, QRef _ q _ b2) -> (b || b2, q)) qsBoth
  qcs = map (\(b, QRef _ _ qc b2) -> (b || b2, qc)) qsBoth
  as = flip mapMaybe lts$ \(_, mix) -> case mix of
    (PureA aref, _) -> Just aref
    (OrMix _ _, cref) -> Just cref
    (AndMix _ aref, _) -> Just aref
    _ -> Nothing
  back = all (\(b, QRef qb _ _ _) -> b || qb) qsBoth
qac (Or ts)
  | null qs0 = do
      c <- newCombined$ Or$ fmap (\(b, (_, t)) -> (b, t)) ts
      return (PureA c, c)
  | null as =
      if back
      then do
        c <- newCombined$ Or$ fmap (\(b, (_, t)) -> (b, t)) ts
        q <- newQDep$ Or$ NE.fromList qs0
        return (PureQ (QRef True (Right q) c False), c)
      else do
        q <- newQDep$ Or$ NE.fromList qs0
        s <- newState q
        c <- newCombined$ State (False, s)
        return (PureQ (QRef False (Right q) c False), c)
  | otherwise = do
      a <- case as of
        [a] -> return a
        _:_:_ -> newCombined$ Or$ NE.fromList$ map (False,) as
      case qsBoth of
        [(b, QRef _ q qc b2)] -> do
          c <- newCombined$ Or$ (b || b2, qc) :| [(False, a)]
          return (OrMix (QRef back q qc (b || b2)) a, c)
        _:_:_
          | back -> do
             q <- newQDep$ Or$ NE.fromList qs0
             qc <- newCombined$ Or$ NE.fromList qcs
             c <- newCombined$ Or$ (False, qc) :| [(False, a)]
             return (OrMix (QRef True (Right q) qc False) a, c)
          | otherwise -> do
             q <- newQDep$ Or$ NE.fromList qs0
             s <- newState q
             qc <- newCombined$ State (False, s)
             c <- newCombined$ Or$ (False, qc) :| [(False, a)]
             return (OrMix (QRef False (Right q) qc False) a, c)
  where
  lts = NE.toList ts
  qsBoth = flip mapMaybe lts$ \(b, fst -> mix) -> (b,) <$> case mix of
    PureQ qref -> Just qref
    OrMix qref _ -> Just qref
    _ -> Nothing
  qs0 = map (\(b, QRef _ q _ b2) -> (b || b2, q)) qsBoth
  qcs = map (\(b, QRef _ _ qc b2) -> (b || b2, qc)) qsBoth
  as = flip mapMaybe lts$ \(_, mix) -> case mix of
    (PureA aref, _) -> Just aref
    (AndMix _ _, cref) -> Just cref
    (OrMix _ aref, _) -> Just aref
    _ -> Nothing
  back = all (\(b, QRef qb _ _ _) -> b || qb) qsBoth


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
    let mappedStates = states <&> \i -> ixMap!i ^._2
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