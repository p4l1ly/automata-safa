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
{-# LANGUAGE StandaloneKindSignatures #-}

module Afa.Finalful where

import Afa.Finalful.STerm (Term (..), (:&:)(..), Create(..), Creation, OneshotFun, OneshotTra)
import qualified Afa.Finalful.STerm as Term
import Control.Lens ( itraverse, (&), traversed, _1, traverseOf)
import Control.Monad ( (<=<) )
import Control.Monad.Free ( Free(Pure, Free) )
import Data.Array ( (!), accumArray, listArray, Array )
import Data.Composition ((.:))
import Data.Fix ( Fix(Fix) )
import Data.Foldable (toList, fold)
import Data.Functor ((<&>))
import Data.Monoid ( Any(..), Endo(..) )
import Data.Traversable (for)
import DepDict (DepDict ((:|:)))
import qualified DepDict as D
import Shaper (FRecK, FunRecur (funRecur), MfnK, Mk, MkN, MonadFn (monadfn), MonadFn', RecK, RecRecur, Recur0 (recur), Recur, ask, IsTree)
import Shaper.Helpers (BuildInheritShareD, BuildD, buildInheritShare, buildFix, buildFree)
import TypeDict (Named(Name), TypeDict (End, LiftTags, (:+:)), d, d', g, g')
import Debug.Trace

data SyncVar q v = VVar v | FVar | QVar q deriving (Eq, Show)
data SyncQs q = QState q | SyncState deriving (Eq, Show)
data Finalness = Final | Complex | Nonfinal deriving (Eq, Show, Ord)

type DRec d rec = Name "rec" rec :+: LiftTags d

type QVR d (q :: *) (v :: *) (r :: *) = (q ~ [g|q|], v ~ [g|v|], r ~ [g|r|])

type RemoveFinalsD d m = RemoveFinalsD_ d m
  (RemoveFinalsA d [g|q|] [g|v|] [g|r|] [g|r'|] m)
  [g|q|] [g|v|] [g|r|] [g|r'|]
type RemoveFinalsA d q v r r' m =
  RemoveFinalsA1 d
    ( Name "term'" (Term (SyncQs q) (SyncVar q v) r')
        :+: Name "termF'" (Term (SyncQs q) (SyncVar q v))
        :+: End
    ) q v r r' m
type RemoveFinalsA1 d d' q v r r' m =
  RemoveFinalsA2 d
    ( Name "buildTree'" (Mk (MfnK [g'|term'|] r') [d|buildTree|])
      :+: Name "shareTree'" (Mk (MfnK r' r') [d|shareTree|])
      :+: Name "deref'" (Mk (MfnK r' [g'|term'|]) [d|deref|])
      :+: Name "alphabetF" ([g|fun|] [Term.Q, Term.V] :: *)
      :+: Name "alphabetFn" ((q -> SyncQs q) :&: (v -> SyncVar q v))
      :+: Name "redirectF" ([g|tra|] '[Term.R] :: *)
      :+: Name "redirectFn" (r' -> m r')
      :+: d'
    ) q r r'
type RemoveFinalsA2 d d' q r r' =
  RemoveFinalsA3 d
    ( Name "refdeD'" (Name "buildTree" [d'|buildTree'|] :+: Name "shareTree" [d'|shareTree'|] :+: Name "deref" [d'|deref'|] :+: d)
      :+: Name "refdeDTree'" (Name "build" [d'|buildTree'|] :+: Name "deref" [d'|deref'|] :+: d)
      :+: d'
    ) q r r'
type RemoveFinalsA3 d d' q r r' =
  Name "alphabet" (Mk (FRecK r r' (Creation [g'|alphabetF|] [g'|alphabetFn|])) [d|funr|])
    :+: Name "finalConstr" (MkN (RecK r' [g'|term'|] r') [d|any|])
    :+: Name "finalConstrD" (Name "r" r' :+: [g'|refdeD'|])
    :+: Name "redirect" (Mk (FRecK r' r' (Creation [g'|redirectF|] [g'|redirectFn|])) [d|funr|])
    :+: d'
type RemoveFinalsD_ d m d' q v r r' =
  D.Name "aliases" (QVR d q v r, d' ~ RemoveFinalsA d q v r r' m, r' ~ [g|r'|])
    :|: D.Name "splitF" (SplitFinals'D d m)
    :|: D.Name
          "functorRecur"
          ( FunRecur [d'|alphabet|] m
          , Create [g'|alphabetF|] [g'|alphabetFn|]
          , FunRecur [d'|redirect|] m
          , Create [g'|redirectF|] [g'|redirectFn|]
          )
    :|: D.Name
          "finalConstr"
          ( D.Name "" (RecRecur [d'|finalConstr|] m)
              :|: D.Remove "rec" (BuildFinalConstraintD [g'|finalConstrD|] m)
          )
    :|: D.Name "buildD'" (BuildD [g'|refdeDTree'|] [g'|termF'|] r' m)
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
  (finalnesses, _, complex) <- splitFinals' @d final qCount q2i

  -- adapt the type, so that new symbols and state could be added
  let mfun = create @[g'|alphabetF|] (QState :&: VVar :: [g'|alphabetFn|])
  changeAlphabet <- [d'|funRecur|alphabet|] mfun

  if all (== Nonfinal) finalnesses
    then do
      qTransitions <- mapM (changeAlphabet . i2r) [0 .. qCount - 1]
      let qrmap = listArray (0, qCount - 1) qTransitions
      init' <- changeAlphabet init
      return (init', (qCount, QState . i2q, (qrmap !), \(QState q) -> q2i q))
    else do
      -- create a final constraint
      finalConstraint <- case complex of
        Nothing -> return Nothing
        Just complex -> do
          complex' <- changeAlphabet complex
          Just
            <$>
              ([d'|recur|finalConstr|]
                (buildFinalConstraint @(DRec [g'|finalConstrD|] [d'|finalConstr|]))
                >>= ($ complex')
              )

      -- build a corresponding term t_q for each state;
      qsubs <-
        finalnesses & itraverse \i ->
          let q = i2q i
          in \case
                Final ->
                  [d'|monadfn|shareTree'|] =<<
                    buildFix @[g'|refdeDTree'|]
                      (Fix $ Or (Fix $ State $ QState q) (Fix $ Var FVar))
                Complex -> do
                  tree <- buildFix @[g'|refdeDTree'|] $
                    (Fix .: Or)
                      (Fix $ And (Fix $ Not (Fix $ Var FVar)) (Fix $ State $ QState q))
                      (Fix $ And (Fix $ Var FVar) (Fix $ Var $ QVar q))
                  [d'|monadfn|shareTree'|] tree
                Nonfinal ->
                  [d'|monadfn|shareTree'|] =<<
                    buildFix @[g'|refdeDTree'|]
                      (Fix $ And (Fix $ State $ QState q) (Fix $ Not $ Fix $ Var FVar))

      let redirectFn = \r ->
            [d'|monadfn|deref'|] r <&> \case
              State (QState q) -> qsubs ! q2i q
              _ -> r
      let mtra = create @[g'|redirectF|] (redirectFn :: [g'|redirectFn|])
      redirect <- [d'|funRecur|redirect|] mtra :: m (r' -> m r')

      qTransitions <- mapM (redirect <=< changeAlphabet . i2r) [0 .. qCount - 1]
      init' <- redirect =<< changeAlphabet init
      case finalConstraint of
        Nothing -> do
          let qrmap = listArray (0, qCount - 1) qTransitions
          return (init', (qCount, QState . i2q, (qrmap !), \(QState q) -> q2i q))
        Just finalConstraint -> do
          syncQRef <- [d'|monadfn|buildTree'|] (State SyncState) >>= [d'|monadfn|shareTree'|]
          syncQTrans <- buildFree @[g'|refdeDTree'|] $
            (Free .: Or)
              (Free $ And (Free $ Not (Free $ Var FVar)) (Pure syncQRef))
              (Free $ And (Free $ Var FVar) (Pure finalConstraint))
          init'' <- [d'|monadfn|buildTree'|] (And syncQRef init')
          let qCount' = qCount + 1
          let i2q' = \case 0 -> SyncState; i -> QState $ i2q $ i - 1
          let q2i' = \case SyncState -> 0; QState q -> q2i q + 1
          let qrmap = listArray (0, qCount) $ syncQTrans : qTransitions
          return (init'', (qCount', i2q', (qrmap !), q2i'))

type SplitFinals'D d m = SplitFinals'D_ d m
  (SplitFinals'A d [g|q|] [g|v|] [g|r|] [g|r'|] m)
  [g|q|] [g|v|] [g|r|] [g|r'|]
type SplitFinals'A :: TypeDict -> * -> * -> * -> * -> (* -> *) -> TypeDict
type SplitFinals'A d q v r r' m =
  SplitFinals'A1 d
    ( Name "term" (Term q v r)
        :+: End
    ) q v r r' m
type SplitFinals'A1 d d' q v r r' m =
  SplitFinals'A2 d
    ( Name "buildTree" (Mk (MfnK [g'|term|] r) [d|buildTree|])
      :+: Name "shareTree" (Mk (MfnK r r) [d|shareTree|])
      :+: Name "deref" (Mk (MfnK r [g'|term|]) [d|deref|])
      :+: d'
    ) q r r'
type SplitFinals'A2 d d' q r r' =
  SplitFinals'A3 d
    ( Name "refdeD" (Name "buildTree" [d'|buildTree|] :+: Name "shareTree" [d'|shareTree|] :+: Name "deref" [d'|deref|] :+: d)
      :+: d'
    ) q r r'
type SplitFinals'A3 d d' q r r' =
  Name "splitF" (MkN (RecK r [g'|term|] (SplitFinalsR r q)) [d|lock|])
    :+: Name "findQs" (MkN (RecK r [g'|term|] (Endo [q])) [d|any|])
    :+: d'
type SplitFinals'D_ :: TypeDict -> (* -> *) -> TypeDict -> * -> * -> * -> * -> DepDict
type SplitFinals'D_ d m d' q v r r' =
  D.Name "aliases" (QVR d q v r, d' ~ SplitFinals'A d q v r r' m, r' ~ [g|r'|])
    :|: D.Name "splitF" (D.Name "" (RecRecur [d'|splitF|] m) :|: D.Remove "rec" (SplitFinalsD [g'|refdeD|] m))
    :|: D.Name "findQs" (D.Name "" (Recur [d'|findQs|] m) :|: D.Remove "rec" (FindQsD d m))
    :|: D.End
splitFinals' ::
  forall d q v r r' m d'.
  D.ToConstraint (SplitFinals'D_ d m d' q v r r') =>
  r ->
  Int ->  -- qCount
  (q -> Int) ->  -- q2i
  m (Array Int Finalness, [q], Maybe r)
splitFinals' final qCount q2i = do
  -- split finals; partition states to final, nonfinal and complex;
  ((_, (`appEndo` []) -> nonfinals), complex) <-
    [d'|recur|splitF|] (splitFinals @(DRec [g'|refdeD|] [d'|splitF|])) >>= ($ final)
  complexFinals <- case complex of
    Nothing -> return []
    Just complex -> ([d'|recur|findQs|] (findQs @(DRec d [d'|findQs|]) @q @v @r) >>= ($ complex)) <&> (`appEndo` [])
  let finalnesses =
        accumArray max Final (0, qCount - 1) $
          map (\q -> (q2i q, Nonfinal)) nonfinals
            ++ map (\q -> (q2i q, Complex)) complexFinals
  return (finalnesses, nonfinals, complex)


type RemoveFinalsHindD d m = RemoveFinalsHindD_ d m
  (RemoveFinalsHindA d [g|q|] [g|v|] [g|r|] [g|r'|] m)
  [g|q|] [g|v|] [g|r|] [g|r'|]
type RemoveFinalsHindA d q v r r' m =
  RemoveFinalsHindA1 d
    ( Name "term'" (Term (SyncQs q) (SyncVar q v) r')
        :+: Name "termF'" (Term (SyncQs q) (SyncVar q v))
        :+: End
    ) q v r r' m
type RemoveFinalsHindA1 d d' q v r r' m =
  RemoveFinalsHindA2 d
    ( Name "buildTree'" (Mk (MfnK [g'|term'|] r') [d|buildTree|])
      :+: Name "shareTree'" (Mk (MfnK r' r') [d|shareTree|])
      :+: Name "deref'" (Mk (MfnK r' [g'|term'|]) [d|deref|])
      :+: Name "alphabetF" ([g|fun|] [Term.Q, Term.V] :: *)
      :+: Name "alphabetFn" ((q -> SyncQs q) :&: (v -> SyncVar q v))
      :+: d'
    ) q r r'
type RemoveFinalsHindA2 d d' q r r' =
  RemoveFinalsHindA3 d
    ( Name "refdeD'" (Name "buildTree" [d'|buildTree'|] :+: Name "shareTree" [d'|shareTree'|] :+: Name "deref" [d'|deref'|] :+: d)
      :+: Name "refdeDTree'" (Name "build" [d'|buildTree'|] :+: Name "deref" [d'|deref'|] :+: d)
      :+: d'
    ) q r r'
type RemoveFinalsHindA3 d d' q r r' =
  Name "alphabet" (Mk (FRecK r r' (Creation [g'|alphabetF|] [g'|alphabetFn|])) [d|funr|])
    :+: Name "finalConstr" (MkN (RecK r' [g'|term'|] r') [d|any|])
    :+: Name "finalConstrD" (Name "r" r' :+: [g'|refdeD'|])
    :+: d'
type RemoveFinalsHindD_ d m d' q v r r' =
  D.Name "aliases" (QVR d q v r, d' ~ RemoveFinalsHindA d q v r r' m, r' ~ [g|r'|])
    :|: D.Name "splitF" (SplitFinals'D d m)
    :|: D.Name
          "functorRecur"
          ( FunRecur [d'|alphabet|] m
          , Create [g'|alphabetF|] [g'|alphabetFn|]
          )
    :|: D.Name
          "finalConstr"
          ( D.Name "" (RecRecur [d'|finalConstr|] m)
              :|: D.Remove "rec" (BuildFinalConstraintD [g'|finalConstrD|] m)
          )
    :|: D.Name "buildD'" (BuildD [g'|refdeDTree'|] [g'|termF'|] r' m)
    :|: D.Name "deref'" (MonadFn [d'|deref'|] m)
    :|: D.End
removeFinalsHind ::
  forall d q v r r' m d'.
  D.ToConstraint (RemoveFinalsHindD_ d m d' q v r r') =>
  r ->
  r ->
  (Int, Int -> q, Int -> [(r, r)], q -> Int) ->
  m (r', (Int, Int -> SyncQs q, Int -> [(r', r')], SyncQs q -> Int))
removeFinalsHind init final (qCount, i2q, i2r, q2i) = do
  (finalnesses, _, complex) <- splitFinals' @d final qCount q2i

  -- adapt the type, so that new symbols and state could be added
  let mfun = create @[g'|alphabetF|] (QState :&: VVar :: [g'|alphabetFn|])
  changeAlphabet <- [d'|funRecur|alphabet|] mfun

  qTransitions <- for [0 .. qCount - 1] $
    mapM (\(a, q) -> (,) <$> changeAlphabet a <*> changeAlphabet q) . i2r
  if all (== Nonfinal) finalnesses
    then do
      let qrmap = listArray (0, qCount - 1) qTransitions
      init' <- changeAlphabet init
      return (init', (qCount, QState . i2q, (qrmap !), \(QState q) -> q2i q))
    else do
      -- create a final constraint
      finalConstraint <- case complex of
        Nothing -> return Nothing
        Just complex -> do
          complex' <- changeAlphabet complex
          Just
            <$>
              ([d'|recur|finalConstr|]
                (buildFinalConstraint @(DRec [g'|finalConstrD|] [d'|finalConstr|]))
                >>= ($ complex')
              )

      init' <- changeAlphabet init
      fvar <- [d'|monadfn|buildTree'|] (Var FVar)
      nfvar <- [d'|monadfn|buildTree'|] (Not fvar) >>= [d'|monadfn|shareTree'|]
      ltrue <- [d'|monadfn|buildTree'|] LTrue
      qTransitions' <-
        for (zip3 (toList finalnesses) qTransitions [0..]) \(f, ts, i2q -> q) -> do
          case f of
            Final -> return $ (fvar, ltrue) : ts
            Nonfinal -> ts & traverseOf (traversed . _1) \a ->
              [d'|monadfn|buildTree'|] (And nfvar a)
            Complex -> do
              finish <- buildFree @[g'|refdeDTree'|]
                (Free $ And (Pure fvar) (Free $ Var $ QVar q))
              ts' <- ts & traverseOf (traversed . _1) \a ->
                [d'|monadfn|buildTree'|] (And nfvar a)
              return $ (finish, ltrue) : ts'
      case finalConstraint of
        Nothing -> do
          let qrmap = listArray (0, qCount - 1) qTransitions'
          return (init', (qCount, QState . i2q, (qrmap !), \(QState q) -> q2i q))
        Just finalConstraint -> do
          syncQRef <- [d'|monadfn|buildTree'|] (State SyncState) >>= [d'|monadfn|shareTree'|]
          syncQTrans <- do
            finish <- [d'|monadfn|buildTree'|] (And fvar finalConstraint)
            return [(finish, ltrue), (nfvar, syncQRef)]
          init'' <- [d'|monadfn|buildTree'|] (And syncQRef init')
          let qCount' = qCount + 1
          let i2q' = \case 0 -> SyncState; i -> QState $ i2q $ i - 1
          let q2i' = \case SyncState -> 0; QState q -> q2i q + 1
          let qrmap = listArray (0, qCount) $ syncQTrans : qTransitions'
          return (init'', (qCount', i2q', (qrmap !), q2i'))


type BuildFinalConstraintD d m =
  BuildFinalConstraintD_ d m (BuildFinalConstraintA d m [g|r|]) [g|q|] [g|v|] [g|r|]
type BuildFinalConstraintA d m r =  -- keyword aliases
  Name "self" (Mk (MfnK () r) [d|rec|])
    :+: Name "rec" (Mk (MfnK r r) [d|rec|])
    :+: End
type BuildFinalConstraintD_ d m d' q v r =  -- dependencies
  D.Name "aliases" (QVR d q v r, d' ~ BuildFinalConstraintA d m r)
    :|: D.Name
          "rec"
          ( D.Name "self" (MonadFn [d'|self|] m)
              :|: D.Name "rec" (MonadFn [d'|rec|] m)
              :|: D.Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
              :|: D.End
          )
    :|: D.Name "build" (D.Remove "isTree" (BuildInheritShareD d (Term (SyncQs q) (SyncVar q v) r) r m))
    :|: D.End
buildFinalConstraint ::
  forall d q v r m d'.
  D.ToConstraint (BuildFinalConstraintD_ d m d' q v r) =>
  Term (SyncQs q) (SyncVar q v) r ->
  m r
buildFinalConstraint (State (QState q)) = buildInheritShare @d $ Var (QVar q)
buildFinalConstraint (And a b) =
  buildInheritShare @d
    =<< And <$> [d'|monadfn|rec|] a <*> [d'|monadfn|rec|] b
buildFinalConstraint (Or a b) =
  buildInheritShare @d
    =<< Or <$> [d'|monadfn|rec|] a <*> [d'|monadfn|rec|] b
buildFinalConstraint (Not a) = buildInheritShare @d . Not =<< [d'|monadfn|rec|] a
buildFinalConstraint _ = [d'|ask|self|]


type FindQsD d m = FindQsD_ d m (FindQsA d [g|q|] [g|r|]) [g|q|] [g|v|] [g|r|]
type FindQsA d q r = Name "rec" (Mk (MfnK r (Endo [q])) [d|rec|]) :+: End
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
type SplitFinalsR r q =
  ( ( Any -- 
    , Endo [q]  -- negated states under conjunction
    )
  , Maybe r
  )
type SplitFinalsD d m = SplitFinalsD_ d m (SplitFinalsA d m [g|q|] [g|r|]) [g|q|] [g|v|] [g|r|]
type SplitFinalsA d m q r =
  Name "self" (Mk (MfnK () r) [d|rec|])
    :+: Name "rec" (Mk (MfnK r (SplitFinalsR r q)) [d|rec|])
    :+: End
type SplitFinalsD_ d m d' q v r =
  D.Name "aliases" (QVR d q v r, d' ~ SplitFinalsA d m q r)
    :|: D.Name "deref" (MonadFn' [d|deref|] r (Term q v r) m)
    :|: D.Name
          "rec"
          ( D.Name "self" (MonadFn [d'|self|] m)
              :|: D.Name "rec" (MonadFn [d'|rec|] m)
              :|: D.Name "isTree" (MonadFn (Mk IsTree [d|rec|]) m)
              :|: D.End
          )
    :|: D.Name "build" (D.Remove "isTree" (BuildInheritShareD d (Term q v r) r m))
    :|: D.End
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
        | getAny (fst qs1) && getAny (fst qs2) ->
            Just <$> buildInheritShare @d (And complex1 complex2)
        | otherwise -> Just <$> [d'|ask|self|]
  LTrue -> return ((Any True, Endo id), Nothing)
  _ -> self'
  where
    self' = [d'|ask|self|] <&> \s -> ((Any False, Endo id), Just s)
