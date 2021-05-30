{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module Afa.Ops.Goblin where

import Debug.Trace

import Data.Bifunctor
import Data.Foldable
import Data.Array.Base (unsafeWrite, unsafeAt, unsafeAccumArray)
import GHC.Exts
import Control.Monad.Free
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
import Control.RecursionSchemes.Utils.NoCons
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Void
import Data.Maybe

import Afa.Lib (listArray')
import Afa.Lib.LiftArray
import Afa
import Afa.Term.Mix
import Afa.Term.Mix.Simplify (deUnary)

{-# INLINABLE goblinUntilFixpoint #-}
goblinUntilFixpoint :: forall p. Show p => AfaUnswallowed p -> AfaUnswallowed p
goblinUntilFixpoint afa = afa'{terms = unmarked} where
  marked = markBack afa
  closure afa = maybe afa (closure . removeUnused)$ goblin2 afa
  afa' = closure$ afa{terms = marked}
  unmarked = terms afa' <&> appMTFun mtfun0{mtfunQ = snd, mtfunT = snd}

data BackEdgeMark p
  = Unvisited
  | Recur
  | Recurring
  | Evaluated (Term p (Bool, Int) (Bool, Int))
  deriving Show

instance Semigroup (BackEdgeMark p) where
  Unvisited <> x = x
  x <> _ = x

{-# INLINABLE markBack #-}
markBack :: forall p. Show p => AfaUnswallowed p
  -> Array Int (Term p (Bool, Int) (Bool, Int))
markBack afa@(Afa terms states init) = runST getMarks &
  \arr -> listArray (bounds arr) (zip [0..] (elems arr)) <&>
    \case (_, Evaluated x) -> x; (i, _) -> error$ show (i, afa)
  where
  getMarks :: forall s. ST s (Array Int (BackEdgeMark p))
  getMarks = do
    marks <- newArray @(STArray s) (bounds terms) Unvisited
    unsafeWrite marks (states `unsafeAt` init) Recur
    dfs (traversal marks) marks (states `unsafeAt` init)
    unsafeFreeze marks

  traversal :: STArray s Int (BackEdgeMark p)
    -> LensLike (ST s) (BackEdgeMark p, Int) Bool (BackEdgeMark p, Int) Bool
  traversal arr rec (x, i) = case x of
    Recur -> do
      unsafeWrite arr i Recurring 
      term' <- terms `unsafeAt` i & modChilds pureChildMod
        { lQ = \q -> (, q) <$> rec (Recur, states `unsafeAt` q)
        , lT = \j -> (, j) <$> rec (Recur, j)
        }
      unsafeWrite arr i (Evaluated term')
      return False
    Recurring -> return True
    Evaluated _ -> return False
    Unvisited -> error "visiting unvisited"

{-# INLINABLE newState #-}
newState :: Monad m => Int -> NoConsT Int m Int
newState = nocons

{-# INLINABLE newCombined #-}
newCombined :: (MonadTrans mt2, Monad (mt (NoConsT x m)), MonadTrans mt, Monad m)
  => x -> mt2 (mt (NoConsT x m)) Int
newCombined = lift . lift . nocons

{-# INLINABLE newQDep #-}
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

{-# INLINABLE qac #-}
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
  as = flip mapMaybe lts$ \(_, mix) -> case mix of
    (PureA aref, _) -> Just aref
    (OrMix _ _, cref) -> Just cref
    (AndMix _ aref, _) -> Just aref
    _ -> Nothing
  qs0 = map (\(b, QRef _ q _ b2) -> (b || b2, q)) qsBoth
  qcs = map (\(b, QRef _ _ qc b2) -> (b || b2, qc)) qsBoth
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
  as = flip mapMaybe lts$ \(_, mix) -> case mix of
    (PureA aref, _) -> Just aref
    (AndMix _ _, cref) -> Just cref
    (OrMix _ aref, _) -> Just aref
    _ -> Nothing
  qs0 = map (\(b, QRef _ q _ b2) -> (b || b2, q)) qsBoth
  qcs = map (\(b, QRef _ _ qc b2) -> (b || b2, qc)) qsBoth
  back = all (\(b, QRef qb _ _ _) -> b || qb) qsBoth


{-# INLINABLE extract #-}
extract
  :: Term p (Bool, Int) (Bool, (Mix, Int))
  -> Free (Term p (Bool, Int)) (Bool, (Mix, Int))
extract LTrue = Free LTrue
extract (Predicate p) = Free (Predicate p)
extract (State q) = Free (State q)
extract (And ts) = case extracted of
  [x] -> x
  (x:xs) -> Free$ And$ x :| xs
  where
  lts = NE.toList ts
  candidates = flip map lts$ \case
    x@(_, (OrMix _ a, _)) -> (Just a, x)
    x@(_, (PureA a, _)) -> (Just a, x)
    x -> (Nothing, x)
  grouped = groupWith fst$ sortWith fst candidates
  extracted = flip map grouped$ \case
    [x] -> Pure$ snd x
    ((a, x):(map snd -> xs)) -> case a of
      Nothing -> Free$ And$ NE.map Pure$ x:|xs
      Just a -> case xs' of
        Right xs' -> Free$ Or$
          Pure (False, (PureA a, a))
          :| [Free$ And$ NE.map Pure xs']
        Left x -> Pure x
        where
        xs' = for (x:|xs)$ \case
          (b, (OrMix q@(QRef _ _ qc _) _, _)) -> Right (b, (PureQ q, qc))
          x -> Left x
extract (Or ts) = case extracted of
  [x] -> x
  (x:xs) -> Free$ Or$ x :| xs
  where
  lts = NE.toList ts
  candidates = flip map lts$ \case
    x@(_, (AndMix _ a, _)) -> (Just a, x)
    x@(_, (PureA a, _)) -> (Just a, x)
    x -> (Nothing, x)
  grouped = groupWith fst$ sortWith fst candidates
  extracted = flip map grouped$ \case
    [x] -> Pure$ snd x
    ((a, x):(map snd -> xs)) -> case a of
      Nothing -> Free$ Or$ NE.map Pure$ x:|xs
      Just a -> case xs' of
        Right xs' -> Free$ And$
          Pure (False, (PureA a, a))
          :| [Free$ Or$ NE.map Pure xs']
        Left x -> Pure x
        where
        xs' = for (x:|xs)$ \case
          (b, (AndMix q@(QRef _ _ qc _) _, _)) -> Right (b, (PureQ q, qc))
          x -> Left x


{-# INLINABLE extractAndQac #-}
extractAndQac
  :: Monad m
  => Term p (Bool, Int) (Bool, (Mix, Int))
  -> NoConsT Int
       ( NoConsT (Term Void Void (Bool, Either (Bool, Int) Int))
           (NoConsT (Term p (Bool, Int) (Bool, Int)) m)
       )
       (Mix, Int)
extractAndQac (extract -> x) = fmap snd$ flip iterM x$
  sequence >=> qac >=> return . (False,)


{-# INLINABLE goblin2 #-}
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
        cataScanT' @(LLLSTArray s) (traversed._2) extractAndQac terms

    let qshift = length aterms
    let mappedStates = states <&> \i -> ixMap `unsafeAt` i ^._2
    let qterms' :: [Term p (Bool, Int) (Bool, Int)]
        qterms' = ($ qterms)$ map$ appMTFun MTFun
          { mtfunP = absurd
          , mtfunQ = absurd
          , mtfunT = \(b, i) -> case i of
              Left (qb, q) -> (b || qb, mappedStates `unsafeAt` q)
              Right t -> (b, t + qshift)
          }

    return$ case statesL of
      [] -> Nothing
      _ -> traceShow (length statesL)$ Just (aterms ++ qterms', elems mappedStates ++ map (+ qshift) statesL)


{-# INLINABLE removeUnused #-}
removeUnused :: forall p.
  Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int
  -> Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int
removeUnused afa@(Afa terms states init) =
  Afa (listArray' terms'') (listArray' states') (qIxMap!init)
  where
  (qmarks, tmarks) = markReachable afa
  termsWithReachability = listArray (bounds tmarks)$ zip (elems tmarks) (elems terms)

  (tIxMap, terms') = runST action
  action :: forall s. ST s (Array Int Int, [Term p (Bool, Int) (Bool, Int)])
  action = runNoConsT$ ($termsWithReachability)$ cataScanT' @(LSTArray s)
    (_2.traversed._2)$ \case
    (False, _) -> return$ error "reaching unreachable child"
    (True, x) -> nocons x

  states' = map ((tIxMap!) . snd)$ filter fst$ zip (elems qmarks) (elems states)
  qIxMap = listArray (bounds states)$
    scanl (\c b -> if b then c + 1 else c) 0 (elems qmarks)
  terms'' = map (appMTFun mtfun0{mtfunQ = second (qIxMap!)}) terms'


data ReachableMark = UnvisitedR | RecurR | VisitedR
instance Semigroup ReachableMark where
  UnvisitedR <> x = x
  x <> _ = x

{-# INLINABLE markReachable #-}
markReachable
  :: Afa (Array Int (Term p (Bool, Int) (Bool, Int))) (Array Int Int) Int
  -> (Array Int Bool, Array Int Bool)
markReachable (Afa terms states init) = (qmarks, termMarks)
  where
  termMarks = runST getMarks <&> \case UnvisitedR -> False; _ -> True

  getMarks :: forall s. ST s (Array Int ReachableMark)
  getMarks = do
    marks <- newArray @(STArray s) (bounds terms) UnvisitedR
    let i = states `unsafeAt` init
    unsafeWrite marks i RecurR
    dfs (traversal marks) marks i
    unsafeFreeze marks

  traversal arr rec (x, i) = case x of
    RecurR -> do
      unsafeWrite arr i VisitedR
      void$ terms `unsafeAt` i & modChilds pureChildMod
        { lQ = \(_, q) -> rec (RecurR, states `unsafeAt` q)
        , lT = \(_, j) -> rec (RecurR, j)
        }
    VisitedR -> return ()
    UnvisitedR -> error "visiting unvisited"

  qmarks = unsafeAccumArray (\_ _ -> True) False (bounds states)$ (init, ()) :
    [ (q, ())
    | (i@(unsafeAt terms -> State (_, q)), True) <- zip [0..] (elems termMarks)
    ]
