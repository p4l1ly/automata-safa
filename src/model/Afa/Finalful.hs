{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Finalful where

import Afa.Finalful.STerm (MFun (..), MTra (..), Term (..))
import Control.Lens (itraverse, (&))
import Control.Monad
import Control.Monad.Free
import Create
import Data.Array
import Data.Composition ((.:))
import Data.Fix
import Data.Foldable (toList)
import Data.Functor ((<&>))
import Data.Monoid
import Data.Traversable (for)
import DepDict (DepDict ((:|:)), (:||:))
import qualified DepDict as D
import Lift (Lift)
import Shaper (Ask (ask), FunRecur (funRecur), Rec, RecRecur, Recur (recur), Transform (transform))
import TypeDict (Get, Name, Tag, TypeDict (LiftTags, (:+:)), d)

data SyncVar q v = VVar v | FVar | QVar q deriving (Eq, Show)
data SyncQs q = QState q | SyncState deriving (Eq, Show)
data Finalness = Final | Complex | Nonfinal deriving (Eq, Show, Ord)

type DRec d rec m = Name "rec" (Rec (Tag rec d) m) :+: LiftTags d

-- |
-- split finals; partition states to final, nonfinal and complex;
-- build a corresponding term t_q for each state;
-- redirect (State q) to t_q in all terms;
type RemoveFinalsD d q v r m r' fun fun2 =
  D.Name
    "splitF"
    ( D.Name "" (RecRecur [d|lock|] r (Term q v r) (SplitFinalsR r q) m)
        :|: D.Name "" (D.Remove "rec" (SplitFinalsD d q v r m))
        :|: D.End
    )
    :|: D.Name
          "findQs"
          ( D.Name "" (Recur [d|any|] r (Term q v r) (Endo [q]) m)
              :|: D.Name "" (D.Remove "rec" (FindQsD d q r m))
              :|: D.End
          )
    :|: D.Name
          "functorRecur"
          ( FunRecur [d|fun|] r r' fun m
          , Create (SyncQs q `Q` SyncVar q v `V` E q v r) fun
          , FunRecur [d|fun2|] r' r' fun2 m
          , Create ( 'MTra (r' `R` E (SyncQs q) (SyncVar q v) r') m) fun2
          )
    :|: D.Name -- TODO build2 and any2 are ugly
          "finalConstr"
          ( D.Name "" (RecRecur [d|any2|] r' (Term (SyncQs q) (SyncVar q v) r') r' m)
              :|: D.Remove "rec" (BuildFinalConstraintD (Name "build" [d|build2|] :+: d) q v r' m)
          )
    -- D.Name "build" (BuildFixD d (Term q (SyncVar q v)) r' m)
    :|: D.Name "newState" (Transform [d|newState|] (SyncQs q, r' -> m r') r' m)
    :|: D.Name "read" (Transform [d|read|] r' (Term (SyncQs q) (SyncVar q v) r') m)
    :|: D.End

-- |
-- existuje mnozstvo typov rekurzie a budeme vyberat taku ktora splna presne to co od nej potrebujeme
-- 1. Rekurzia pri splitovani koncovych stavov je neuplna a vyuziva self (lockuje modifikacie)
-- 2. Rekurzia pri findQs je neuplna
-- 3. Nasledne premapujeme vsetky q, v a to je rekurzia zachovavajuca referencie a meniaca typ.
-- 4. Kedze realne nic nemodifikujeme, mozeme O(1) premapovat complex referenciu z 1. a kopirujuc
--    (tj. bez self, presnejsie, self sa da pouzivat ak nemame pod sebou stav)
--    vybuildit constraint na koncovy symbol
-- 5. (Nezachovavajucim) premapovanim vieme presmerovat r(State q) na qsub!q
removeFinals ::
  forall d q v r m r' fun fun2.
  ( D.ToConstraint (RemoveFinalsD d q v r m r' fun fun2)
  ) =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  m (r', (Int, Int -> SyncQs q, Int -> r', SyncQs q -> Int))
removeFinals init final (qCount, i2q, i2r, q2i) = do
  -- split finals; partition states to final, nonfinal and complex;
  ((_, (`appEndo` []) -> nonfinals), complex) <- [d|recur|lock|] (splitFinals @(DRec d "lock" m)) final
  complexFinals <- case complex of
    Nothing -> return []
    Just complex -> [d|recur|any|] (findQs @(DRec d "any" m)) complex <&> (`appEndo` [])
  let finalnesses =
        accumArray max Final (1, qCount) $
          map (\q -> (q2i q, Nonfinal)) nonfinals
            ++ map (\q -> (q2i q, Complex)) complexFinals

  -- adapt the type, so that new symbols and state could be added
  let mfun = create @MFun @(SyncQs q `Q` SyncVar q v `V` E q v r) @fun QState VVar
  convert <- [d|funRecur|fun|] mfun :: m (r -> m r')

  -- create a final constraint
  finalConstraint <- case complex of
    Nothing -> return Nothing
    Just complex -> do
      complex' <- convert complex
      Just <$> [d|recur|any2|] (buildFinalConstraint @(DRec (Name "build" [d|build2|] :+: d) "any2" m) @q) complex'

  -- build a corresponding term t_q for each state;
  qsubs <-
    finalnesses & itraverse \i ->
      let q = i2q i
       in \case
            Final -> buildFix @(Name "build" [d|build2|] :+: d) $ Fix $ Or (Fix $ State $ QState q) (Fix $ Var FVar)
            Complex ->
              buildFix @(Name "build" [d|build2|] :+: d) $
                (Fix .: Or)
                  (Fix $ And (Fix $ Not (Fix $ Var FVar)) (Fix $ State $ QState q))
                  (Fix $ And (Fix $ Var FVar) (Fix $ Var $ QVar q))
            Nonfinal -> buildFix @(Name "build" [d|build2|] :+: d) $ Fix $ And (Fix $ State $ QState q) (Fix $ Not $ Fix $ Var FVar)

  let mfun2 = create @MTra @( 'MTra (r' `R` E (SyncQs q) (SyncVar q v) r') m) @fun2 $ \r ->
        [d|transform|read|] r <&> \case
          State (QState q) -> (qsubs ! q2i q)
          _ -> r
  convert' <- [d|funRecur|fun2|] mfun2 :: m (r' -> m r')

  case finalConstraint of
    Nothing -> do
      init' <- convert init
      qrmap <- listArray (0, qCount - 1) <$> mapM (convert' <=< convert . i2r) [0 .. qCount - 1]
      return (init', (qCount, QState . i2q, (qrmap !), \(QState q) -> q2i q))
    Just finalConstraint -> do
      syncState <- [d|transform|newState|] . (SyncState,) $ \syncState ->
        buildFree @(Name "build" [d|build2|] :+: d) $
          (Free .: Or)
            (Free $ And (Free $ Not (Free $ Var FVar)) (Pure syncState))
            (Free $ And (Free $ Var FVar) (Pure finalConstraint))
      init' <- convert init
      init'' <- [d|transform|build2|] (And syncState init')
      let qCount' = qCount + 1
      let i2q' = \case 0 -> SyncState; i -> QState $ i2q $ i - 1
      let q2i' = \case SyncState -> 0; QState q -> q2i q + 1
      qrmap <- listArray (0, qCount) . (syncState :) <$> mapM (convert' <=< convert . i2r) [0 .. qCount - 1]
      return (init'', (qCount', i2q', (qrmap !), q2i'))

type BuildFinalConstraintD d q v r m =
  D.Name "build" (Transform [d|build|] (Term (SyncQs q) (SyncVar q v) r) r m)
    :|: D.Name
          "rec"
          ( D.Name "self" (Ask [d|rec|] r m)
              :|: D.Name "rec" (Transform [d|rec|] r r m)
              :|: D.End
          )
    :|: D.End
buildFinalConstraint ::
  forall d q v r m.
  D.ToConstraint (BuildFinalConstraintD d q v r m) =>
  Term (SyncQs q) (SyncVar q v) r ->
  m r
buildFinalConstraint (State (QState q)) = [d|transform|build|] $ Var (QVar q)
buildFinalConstraint (And a b) =
  [d|transform|build|]
    =<< And <$> [d|transform|rec|] a <*> [d|transform|rec|] b
buildFinalConstraint (Or a b) =
  [d|transform|build|]
    =<< Or <$> [d|transform|rec|] a <*> [d|transform|rec|] b
buildFinalConstraint (Not a) = [d|transform|build|] . Not =<< [d|transform|rec|] a
buildFinalConstraint _ = [d|ask|rec|]

type BuildFixD d f r m = D.Name "build" (Transform [d|build|] (f r) r m) :|: D.End
buildFix ::
  forall d f r m.
  (D.ToConstraint (BuildFixD d f r m), Traversable f) =>
  Fix f ->
  m r
buildFix (Fix fa) = traverse (buildFix @d) fa >>= [d|transform|build|]

type BuildFreeD d f r m = D.Name "build" (Transform [d|build|] (f r) r m) :|: D.End
buildFree ::
  forall d f r m.
  (D.ToConstraint (BuildFixD d f r m), Traversable f) =>
  Free f r ->
  m r
buildFree = iterM ([d|transform|build|] <=< sequence)

type FindQsD d q r m = D.Name "rec" (Transform [d|rec|] r (Endo [q]) m) :|: D.End
findQs :: forall d q r v m. D.ToConstraint (FindQsD d q r m) => Term q v r -> m (Endo [q])
findQs (State q) = return $ Endo (q :)
findQs _ = return $ Endo id

-- | Find states, negations of which are in conjunction with the rest.
-- >>> :set -XPartialTypeSignatures
-- >>> import Data.Fix (Fix (Fix))
-- >>> import Shaper (runFixRecur, ReadFix)
-- >>> type ReadFix' = ReadFix (Term Integer ())
-- >>> runFixRecur (splitFinals @() @ReadFix' @()) $ Fix $ Not $ Fix $ State 1
-- ([1],Nothing)
-- >>> runFixRecur (splitFinals @() @ReadFix' @()) $ Fix $ State 1
-- ([],Just (Fix (State 1)))
-- >>> :{
--   runFixRecur (splitFinals @() @ReadFix' @()) $
--     Fix $ And
--       ( Fix $ Not $ Fix $ State 1 )
--       ( Fix $ And
--            ( Fix $ Not $ Fix $ State 2 )
--            ( Fix $ Or
--                ( Fix $ Not $ Fix $ State 3 )
--                ( Fix $ Not $ Fix $ State 4 )
--            )
--       )
-- :}
-- ([1,2],Just (Fix (Or (Fix (Not (Fix (State 3)))) (Fix (Not (Fix (State 4)))))))
type SplitFinalsR r q = ((Any, Endo [q]), Maybe r)

type SplitFinalsD d q v r m =
  D.Name "deref" (Transform [d|deref|] r (Term q v r) m)
    :|: D.Name "build" (Transform [d|build|] (Term q v r) r m)
    :|: D.Name
          "rec"
          ( D.Name "self" (Ask [d|rec|] r m)
              :|: D.Name "rec" (Transform [d|rec|] r (SplitFinalsR r q) m)
              :|: D.End
          )
    :|: D.End
splitFinals ::
  forall d q v r m.
  (D.ToConstraint (SplitFinalsD d q v r m)) =>
  Term q v r ->
  m (SplitFinalsR r q)
splitFinals = \case
  Not r -> do
    child <- [d|transform|deref|] r
    case child of State q -> return ((Any True, Endo (q :)), Nothing); _ -> self'
  And r1 r2 -> do
    (qs1, mcomplex1) <- [d|transform|rec|] r1
    (qs2, mcomplex2) <- [d|transform|rec|] r2
    (qs1 <> qs2,) <$> case (mcomplex1, mcomplex2) of
      (Nothing, Nothing) -> return Nothing
      (Nothing, Just complex2) -> return $ Just complex2
      (Just complex1, Nothing) -> return $ Just complex1
      (Just complex1, Just complex2)
        | getAny (fst qs1) && getAny (fst qs2) -> Just <$> [d|ask|rec|]
        | otherwise -> Just <$> [d|transform|build|] (And complex1 complex2)
  _ -> self'
  where
    self' = [d|ask|rec|] <&> \s -> ((Any False, Endo id), Just s)
