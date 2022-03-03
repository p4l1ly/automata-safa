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
import Data.Foldable (toList, fold)
import Data.Functor ((<&>))
import Data.Monoid
import Data.Traversable (for)
import DepDict (DepDict ((:|:)), (:||:))
import qualified DepDict as D
import Lift (Lift)
import Shaper (FRecK, FunRecur (funRecur), MfnK, MonadFn (monadfn), MonadFn', RecK, RecRecur, Recur (recur), ask)
import TypeDict (Get, Name, Tag, TypeDict (End, LiftTags, (:+:)), d, d', g, g')

data SyncVar q v = VVar v | FVar | QVar q deriving (Eq, Show)
data SyncQs q = QState q | SyncState deriving (Eq, Show)
data Finalness = Final | Complex | Nonfinal deriving (Eq, Show, Ord)

type DRec d rec = Name "rec" rec :+: LiftTags d

type QVR d (q :: *) (v :: *) (r :: *) = (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|])

-- |
-- split finals; partition states to final, nonfinal and complex;
-- build a corresponding term t_q for each state;
-- redirect (State q) to t_q in all terms;
-- |
-- existuje mnozstvo typov rekurzie a budeme vyberat taku ktora splna presne to co od nej potrebujeme
-- 1. Rekurzia pri splitovani koncovych stavov je neuplna a vyuziva self (lockuje modifikacie)
-- 2. Rekurzia pri findQs je neuplna
-- 3. Nasledne premapujeme vsetky q, v a to je rekurzia zachovavajuca referencie a meniaca typ.
-- 4. Kedze realne nic nemodifikujeme, mozeme O(1) premapovat complex referenciu z 1. a kopirujuc
--    (tj. bez self, presnejsie, self sa da pouzivat ak nemame pod sebou stav)
--    vybuildit constraint na koncovy symbol
-- 5. (Nezachovavajucim) premapovanim vieme presmerovat r(State q) na qsub!q
type RemoveFinalsD d m = RemoveFinalsD_ d m
  (RemoveFinalsA d [g|q|] [g|v|] [g|r|] [g|r'|] m)
  [g|q|] [g|v|] [g|r|] [g|r'|]
type RemoveFinalsA d q v r r' m =
  RemoveFinalsA1 d
    ( Name "term" (Term q v r)
        :+: Name "term'" (Term (SyncQs q) (SyncVar q v) r')
        :+: Name "termF'" (Term (SyncQs q) (SyncVar q v))
        :+: Name "alphabetK" (SyncQs q `Q` SyncVar q v `V` E q v r)
        :+: Name "redirectK" ( 'MTra (r' `R` E (SyncQs q) (SyncVar q v) r') m)
        :+: End
    ) q r r'
type RemoveFinalsA1 d d' q r r' =
  RemoveFinalsA2 d
    ( Name "build" (MfnK [d|build|] [g'|term|] r)
      :+: Name "build'" (MfnK [d|build|] [g'|term'|] r')
      :+: Name "deref" (MfnK [d|deref|] r [g'|term|])
      :+: Name "deref'" (MfnK [d|deref|] r' [g'|term'|])
      :+: Name "alphabetF" ([g|fun|] ([g'|alphabetK|] :: MFun) :: *)
      :+: Name "redirectF" ([g|tra|] ([g'|redirectK|] :: MTra) :: *)
      :+: d'
    ) q r r'
type RemoveFinalsA2 d d' q r r' =
  RemoveFinalsA3 d
    ( Name "refdeD" (Name "build" [d'|build|] :+: Name "deref" [d'|deref|] :+: d)
      :+: Name "refdeD'" (Name "build" [d'|build'|] :+: Name "deref" [d'|deref'|] :+: d)
      :+: d'
    ) q r r'
type RemoveFinalsA3 d d' q r r' =
  Name "splitF" (RecK [d|lock|] r [g'|term|] (SplitFinalsR r q))
    :+: Name "findQs" (RecK [d|any|] r [g'|term|] (Endo [q]))
    :+: Name "alphabet" (FRecK [d|funr|] r r' [g'|alphabetF|])
    :+: Name "finalConstr" (RecK [d|any|] r' [g'|term'|] r')
    :+: Name "finalConstrD" (Name "r" r' :+: [g'|refdeD'|])
    :+: Name "redirect" (FRecK [d|funr|] r' r' [g'|redirectF|])
    :+: d'
type RemoveFinalsD_ d m d' q v r r' =
  D.Name "aliases" (QVR d q v r, d' ~ RemoveFinalsA d q v r r' m, r' ~ [g|r'|])
    :|: D.Name "splitF" (D.Name "" (RecRecur [d'|splitF|] m) :|: D.Remove "rec" (SplitFinalsD [g'|refdeD|] m))
    :|: D.Name "findQs" (D.Name "" (Recur [d'|findQs|] m) :|: D.Remove "rec" (FindQsD d m))
    :|: D.Name
          "functorRecur"
          ( FunRecur [d'|alphabet|] m
          , Create ([g'|alphabetK|] :: MFun) [g'|alphabetF|]
          , FunRecur [d'|redirect|] m
          , Create ([g'|redirectK|] :: MTra) [g'|redirectF|]
          )
    :|: D.Name
          "finalConstr"
          ( D.Name "" (RecRecur [d'|finalConstr|] m)
              :|: D.Remove "rec" (BuildFinalConstraintD [g'|finalConstrD|] m)
          )
    :|: D.Name "buildD'" (BuildD [g'|refdeD'|] [g'|termF'|] r' m)
    :|: D.Name "deref'" (MonadFn [d'|deref'|] m)
    :|: D.End
removeFinals ::
  forall d q v r r' m d'.
  D.ToConstraint (RemoveFinalsD_ d m d' q v r r') =>
  r ->
  r ->
  (Int, Int -> q, Int -> r, q -> Int) ->
  m (r', (Int, Int -> SyncQs q, Int -> r', SyncQs q -> Int))
removeFinals init final (qCount, i2q, i2r, q2i) = do
  -- split finals; partition states to final, nonfinal and complex;
  ((_, (`appEndo` []) -> nonfinals), complex) <-
    [d'|recur|splitF|] (splitFinals @(DRec [g'|refdeD|] [d'|splitF|])) final
  complexFinals <- case complex of
    Nothing -> return []
    Just complex -> [d'|recur|findQs|] (findQs @(DRec d [d'|findQs|]) @q @v @r) complex <&> (`appEndo` [])
  let finalnesses =
        accumArray max Final (1, qCount) $
          map (\q -> (q2i q, Nonfinal)) nonfinals
            ++ map (\q -> (q2i q, Complex)) complexFinals

  -- adapt the type, so that new symbols and state could be added
  let mfun = create @MFun @([g'|alphabetK|] :: MFun) @[g'|alphabetF|] QState VVar
  changeAlphabet <- [d'|funRecur|alphabet|] mfun

  -- create a final constraint
  finalConstraint <- case complex of
    Nothing -> return Nothing
    Just complex -> do
      complex' <- changeAlphabet complex
      Just
        <$> [d'|recur|finalConstr|]
          (buildFinalConstraint @(DRec [g'|finalConstrD|] [d'|finalConstr|]))
          complex'

  -- build a corresponding term t_q for each state;
  qsubs <-
    finalnesses & itraverse \i ->
      let q = i2q i
       in \case
            Final -> buildFix @[g'|refdeD'|] $ Fix $ Or (Fix $ State $ QState q) (Fix $ Var FVar)
            Complex ->
              buildFix @[g'|refdeD'|] $
                (Fix .: Or)
                  (Fix $ And (Fix $ Not (Fix $ Var FVar)) (Fix $ State $ QState q))
                  (Fix $ And (Fix $ Var FVar) (Fix $ Var $ QVar q))
            Nonfinal -> buildFix @[g'|refdeD'|] $ Fix $ And (Fix $ State $ QState q) (Fix $ Not $ Fix $ Var FVar)

  let mtra = create @MTra @([g'|redirectK|] :: MTra) @[g'|redirectF|] $ \r ->
        [d'|monadfn|deref'|] r <&> \case
          State (QState q) -> (qsubs ! q2i q)
          _ -> r
  redirect <- [d'|funRecur|redirect|] mtra :: m (r' -> m r')
  qTransitions <- mapM (redirect <=< changeAlphabet . i2r) [0 .. qCount - 1]

  case finalConstraint of
    Nothing -> do
      init' <- changeAlphabet init
      let qrmap = listArray (0, qCount - 1) qTransitions
      return (init', (qCount, QState . i2q, (qrmap !), \(QState q) -> q2i q))
    Just finalConstraint -> do
      syncQRef <- [g'|monadfn|build'|] (State SyncState)
      syncQTrans <- buildFree @[g'|refdeD'|] $
        (Free .: Or)
          (Free $ And (Free $ Not (Free $ Var FVar)) (Pure syncQRef))
          (Free $ And (Free $ Var FVar) (Pure finalConstraint))
      init' <- changeAlphabet init
      init'' <- [d'|monadfn|build'|] (And syncQRef init')
      let qCount' = qCount + 1
      let i2q' = \case 0 -> SyncState; i -> QState $ i2q $ i - 1
      let q2i' = \case SyncState -> 0; QState q -> q2i q + 1
      let qrmap = listArray (0, qCount) $ syncQTrans : qTransitions
      return (init'', (qCount', i2q', (qrmap !), q2i'))


type BuildFinalConstraintD d m =
  BuildFinalConstraintD_ d m (BuildFinalConstraintA d m [g|r|]) [g|q|] [g|v|] [g|r|]
type BuildFinalConstraintA d m r =  -- keyword aliases
  Name "self" (MfnK [d|rec|] () r)
    :+: Name "rec" (MfnK [d|rec|] r r)
    :+: End
type BuildFinalConstraintD_ d m d' q v r =  -- dependencies
  D.Name "aliases" (QVR d q v r, d' ~ BuildFinalConstraintA d m r)
    :|: D.Name
          "rec"
          ( D.Name "self" (MonadFn [d'|self|] m)
              :|: D.Name "rec" (MonadFn [d'|rec|] m)
              :|: D.End
          )
    :|: BuildD d (Term (SyncQs q) (SyncVar q v)) r m
buildFinalConstraint ::
  forall d q v r m d'.
  D.ToConstraint (BuildFinalConstraintD_ d m d' q v r) =>
  Term (SyncQs q) (SyncVar q v) r ->
  m r
buildFinalConstraint (State (QState q)) = [d|monadfn|build|] $ Var (QVar q)
buildFinalConstraint (And a b) =
  [d|monadfn|build|]
    =<< And <$> [d'|monadfn|rec|] a <*> [d'|monadfn|rec|] b
buildFinalConstraint (Or a b) =
  [d|monadfn|build|]
    =<< Or <$> [d'|monadfn|rec|] a <*> [d'|monadfn|rec|] b
buildFinalConstraint (Not a) = [d|monadfn|build|] . Not =<< [d'|monadfn|rec|] a
buildFinalConstraint _ = [d'|ask|self|]


type BuildD d f r m = D.Name "build" (MonadFn' [d|build|] (f r) r m) :|: D.End
buildFix ::
  forall d f r m.
  (D.ToConstraint (BuildD d f r m), Traversable f) =>
  Fix f ->
  m r
buildFix (Fix fa) = traverse (buildFix @d) fa >>= [d|monadfn|build|]

buildFree ::
  forall d f r m.
  (D.ToConstraint (BuildD d f r m), Traversable f) =>
  Free f r ->
  m r
buildFree = iterM ([d|monadfn|build|] <=< sequence)


type FindQsD d m = FindQsD_ d m (FindQsA d [g|q|] [g|r|]) [g|q|] [g|v|] [g|r|]
type FindQsA d q r = Name "rec" (MfnK [d|rec|] r (Endo [q])) :+: End
type FindQsD_ d m d' q v r =
  D.Name "aliases" (QVR d q v r, d' ~ FindQsA d q r)
  :|: D.Name "rec" (MonadFn [d'|rec|] m) :|: D.End
findQs ::
  forall d q v r m d'.
  D.ToConstraint (FindQsD_ d m d' q v r)
  => Term q v r -> m (Endo [q])
findQs (State q) = return $ Endo (q :)
findQs f = fold <$> mapM [d'|monadfn|rec|] f


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
type SplitFinalsD d m = SplitFinalsD_ d m (SplitFinalsA d m [g|q|] [g|r|]) [g|q|] [g|v|] [g|r|]
type SplitFinalsA d m q r =
  Name "self" (MfnK [d|rec|] () r)
    :+: Name "rec" (MfnK [d|rec|] r (SplitFinalsR r q))
    :+: End
type SplitFinalsD_ d m d' q v r =
  D.Name "aliases" (QVR d q v r, d' ~ SplitFinalsA d m q r)
    :|: D.Name "deref" (MonadFn' [d|deref|] r (Term q v r) m)
    :|: D.Name "build" (MonadFn' [d|build|] (Term q v r) r m)
    :|: D.Name
          "rec"
          ( D.Name "self" (MonadFn [d'|self|] m)
              :|: D.Name "rec" (MonadFn [d'|rec|] m)
              :|: D.End
          )
    :|: BuildD d (Term q v) r m
splitFinals ::
  forall d q v r m d'.
  D.ToConstraint (SplitFinalsD_ d m d' q v r) =>
  Term q v r ->
  m (SplitFinalsR r q)
splitFinals = \case
  Not r -> do
    child <- [d|monadfn|deref|] r
    case child of State q -> return ((Any True, Endo (q :)), Nothing); _ -> self'
  And r1 r2 -> do
    (qs1, mcomplex1) <- [d'|monadfn|rec|] r1
    (qs2, mcomplex2) <- [d'|monadfn|rec|] r2
    (qs1 <> qs2,) <$> case (mcomplex1, mcomplex2) of
      (Nothing, Nothing) -> return Nothing
      (Nothing, Just complex2) -> return $ Just complex2
      (Just complex1, Nothing) -> return $ Just complex1
      (Just complex1, Just complex2)
        | getAny (fst qs1) && getAny (fst qs2) -> Just <$> [d'|ask|self|]
        | otherwise -> Just <$> [d|monadfn|build|] (And complex1 complex2)
  _ -> self'
  where
    self' = [d'|ask|self|] <&> \s -> ((Any False, Endo id), Just s)
