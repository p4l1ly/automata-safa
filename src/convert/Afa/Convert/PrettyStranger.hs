{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Afa.Convert.PrettyStranger where

import Afa
import Afa.Bool
import Afa.Lib (listArray')
import Afa.Lib.Free
import Afa.Lib.LiftArray
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Bool.Simplify as BTerm
import qualified Afa.Term.Mix as MTerm
import qualified Afa.Term.Mix.Simplify as MTerm
import Control.Applicative
import Control.Arrow
import Control.Lens
import Control.Monad.Free
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Trans (lift)
import Control.Monad.Writer
import Control.RecursionSchemes.Lens
import Control.RecursionSchemes.Utils.HashCons
import Control.RecursionSchemes.Utils.NoCons
import Data.Array
import Data.Array.ST
import Data.Attoparsec.Expr
import Data.Attoparsec.Text
import qualified Data.Attoparsec.Text as Parsec
import Data.Char
import Data.Composition ((.:))
import Data.Fix hiding (cata)
import Data.Functor.Classes
import Data.Functor.Compose
import qualified Data.HashMap.Strict as HM
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromJust, isNothing)
import Data.Monoid (Ap (..), Endo (..))
import Data.String.Interpolate.IsString
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import Data.Traversable
import Debug.Trace
import GHC.Generics hiding (Infix, Prefix)
import Generic.Data (Generically1 (..))
import Generic.Data.Orphans ()

parseWhole :: Parser a -> T.Text -> a
parseWhole parser str = case parse parser str of
  Fail i ctxs err -> error $ show (i, ctxs, err)
  Partial p -> case p "" of
    Fail i ctxs err -> error $ show (i, ctxs, err)
    Partial _ -> error "expr double partial"
    Done _ x -> x
  Done _ x -> x

parseAfa :: T.Text -> BoolAfaUnswallowed Int
parseAfa str = toAfa (length states) (length formulae) acount init final states formulae
  where
    str' = T.filter (not . isSpace) str
    parser =
      many $
        parseOne
          <$> (char '@' *> Parsec.takeWhile (/= ':') <* char ':')
          <*> Parsec.takeWhile (/= '@')
    ((init, final, states, formulae), acount) = enumerate $ parseWhole parser str'

data Definition
  = DInitialStates {dterm :: Fix STermStr}
  | DFinalStates {dterm :: Fix STermStr}
  | DFormula {name :: T.Text, dterm :: Fix STermStr}
  | DState {name :: T.Text, dterm :: Fix STermStr}

type STermStr = STerm T.Text T.Text T.Text

type STerm' = STerm Int Int Int

parseOne :: T.Text -> T.Text -> Definition
parseOne name value = case T.uncons name of
  Just ('f', name') -> DFormula name' $ parseWhole expr value
  Just ('s', name') -> DState name' $ parseWhole expr value
  Just ('k', keyword) -> case keyword of
    "InitialFormula" -> DInitialStates $ parseWhole expr value
    "FinalFormula" -> DFinalStates $ parseWhole expr value
    _ -> error [i|unknown keyowrd #{keyword}|]
  Just (t, _) -> error [i|unknown type #{t}|]
  Nothing -> error "empty identifier"

u :: Endo [a] -> [a]
u = (`appEndo` [])

recur :: ((a -> b) -> a -> b) -> a -> b
recur fn = rec where rec = fn rec

enumerate :: [Definition] -> ((Fix STerm', Fix STerm', [Fix STerm'], [Fix STerm']), Int)
enumerate defs =
  second length . runIdentity . runHashConsT $
    (,,,)
      <$> namesToIxs (orize init)
      <*> namesToIxs (orize final)
      <*> mapM (namesToIxs . snd) orStates
      <*> mapM (namesToIxs . snd) orFormulae
  where
    orize [] = Fix SFalse
    orize xs = foldr1 (Fix .: SOr) xs

    (u -> init, u -> final, u -> states, u -> formulae) = execWriter $
      for defs $ \case
        DFormula name dterm -> tell (mempty, mempty, mempty, Endo ((name, dterm) :))
        DState name dterm -> tell (mempty, mempty, Endo ((name, dterm) :), mempty)
        DInitialStates dterm -> tell (Endo (dterm :), mempty, mempty, mempty)
        DFinalStates dterm -> tell (mempty, Endo (dterm :), mempty, mempty)

    orFormulaeHM = HM.fromListWith (Fix .: SOr) formulae
    orFormulae = HM.toList orFormulaeHM
    orStates = HM.toList $ HM.fromListWith (Fix .: SOr) states

    (fNameToIx, _) = flip execState (HM.empty, 0) $ for orFormulae $ fRec . fst
      where
        fRec name =
          gets ((HM.!? name) . fst) >>= \case
            Just Nothing -> error [i|cycle #{name}|]
            Just _ -> return ()
            Nothing -> do
              modify $ first (HM.insert name Nothing)
              let formula = orFormulaeHM HM.! name
              let fRecAll rRec = unFix >>> appMTFol mtfol0{mtfolF = Ap . fRec, mtfolR = rRec}
              getAp $ recur fRecAll formula
              modify $ \(m, i) -> (HM.insert name (Just i) m, i + 1)
    qNameToIx = HM.fromList $ zip (map fst orStates) [0 ..]

    namesToIxs :: Fix STermStr -> HashConsT T.Text T.Text Identity (Fix STerm')
    namesToIxs =
      unFix
        >>> appMTTra
          MTTra
            { mttraV = hashCons'
            , mttraQ = return . (qNameToIx HM.!)
            , mttraF = return . fromJust . (fNameToIx HM.!)
            , mttraR = namesToIxs
            }
        >>> fmap Fix

expr :: Parser (Fix STermStr)
expr = buildExpressionParser table term <?> "expression"
  where
    table =
      [ [Prefix $ Fix . SNot <$ char '!']
      , [Infix (Fix .: SAnd <$ char '&') AssocLeft]
      , [Infix (Fix .: SOr <$ char '|') AssocLeft]
      ]

identifier = Parsec.takeWhile (\case '_' -> True; x -> isAlphaNum x)

term :: Parser (Fix STermStr)
term =
  "(" *> expr <* ")"
    <|> (Fix . SState <$> ("s" *> identifier))
    <|> (Fix . SFormula <$> ("f" *> identifier))
    <|> (Fix STrue <$ "True")
    <|> (Fix SFalse <$ "False")
    <|> (Fix . SVar <$> identifier)
    <?> "expected a term"

convertFormulae ::
  [Fix STerm'] ->
  Int ->
  Int ->
  Int ->
  ( Array Int (Bool, Int)
  , [Free (BTerm.Term Int) Int]
  , [Free (MTerm.Term (Free (BTerm.Term Int) Int) Int) Int]
  )
convertFormulae formulae fcount qcount acount = runST action
  where
    action :: forall s. ST s (Array Int (Bool, Int), [Free (BTerm.Term Int) Int], [Free (MTerm.Term (Free (BTerm.Term Int) Int) Int) Int])
    action = do
      let formulaeArr = listArray (0, fcount - 1) formulae
      ((ixMap0, fbterms0), fmterms0) <- runNoConsTFrom qcount . runNoConsTFrom (4 + acount) $
        ($ formulaeArr) $
          cataScanT' @(LLSTArray s)
            (\rec -> cataT recursiveTraversal $ fmap Fix . appMTTra mttra0{mttraF = rec})
            $ \f -> do
              let f' = ($ f) $
                    cataRecursive $ \case
                      STrue -> Left $ Pure 0
                      SFalse -> Left $ Pure 1
                      SState q -> Right $ Pure q
                      SFormula (False, i) -> Left $ Pure i
                      SFormula (True, i) -> Right $ Pure i
                      SVar v -> Left $ Pure (v + 4)
                      SNot (Left x) -> Left $ Free $ BTerm.Not x
                      SNot (Right _) -> error "negation above states"
                      SAnd (Left x) (Left y) -> Left $ Free $ BTerm.And $ x :| [y]
                      SOr (Left x) (Left y) -> Left $ Free $ BTerm.Or $ x :| [y]
                      SAnd x y -> Right $ Free $ MTerm.And $ NE.map asRight $ x :| [y]
                      SOr x y -> Right $ Free $ MTerm.Or $ NE.map asRight $ x :| [y]
              case f' of
                Left bterm -> (False,) <$> nocons bterm
                Right mterm -> (True,) <$> lift (nocons mterm)
      return (ixMap0, fbterms0, fmterms0)

asRight (Left x) = Free $ MTerm.Predicate x
asRight (Right x) = x

toAfa ::
  Int ->
  Int ->
  Int ->
  Fix STerm' ->
  Fix STerm' ->
  [Fix STerm'] ->
  [Fix STerm'] ->
  BoolAfaUnswallowed Int
toAfa qcount fcount acount init final states formulae =
  unswallow $
    BoolAfa
      { boolTerms =
          listArray' $
            [ Free BTerm.LTrue
            , Free BTerm.LFalse
            , Free $ BTerm.Predicate qcount
            , Free $ BTerm.Not $ Pure 2
            ]
              ++ map (Free . BTerm.Predicate) [qcount + 1 .. qcount + acount]
              ++ fbterms
      , Afa.Bool.afa =
          Afa
            { terms = listArray' $ extendedStates ++ fmterms
            , states = states''
            , initState = init''
            }
      }
  where
    (simpleNonfinal, nonsimpleFinal) = finalSplitSimple qcount final

    nonsimpleFinal' =
      (nonsimpleFinal <&>) $
        cataRecursive $
          getCompose >>> \case
            [x] -> alg x
            xs -> Free $ BTerm.And $ NE.fromList $ xs <&> alg
      where
        alg = \case
          SState q
            | simpleNonfinal ! q -> Pure 1
            | otherwise -> Free $ BTerm.Predicate q
          SNot x -> Free $ BTerm.Not x
          SAnd a b -> Free $ BTerm.And $ a :| [b]
          SOr a b -> Free $ BTerm.Or $ a :| [b]
          STrue -> Pure 0
          SFalse -> Pure 1
          SVar _ -> error "variable in kFinalFormula"
          SFormula _ -> error "unsupported: formula in kFinalFormula"

    nonsimpleFinal'' =
      nonsimpleFinal' <&> \fq ->
        Free $
          MTerm.Or $
            Free (MTerm.And $ Free (MTerm.State $ qcount + 1) :| [Free $ MTerm.Predicate $ Pure 3])
              :| [Free $ MTerm.And $ Free (MTerm.Predicate $ Pure 2) :| [Free $ MTerm.Predicate fq]]

    qsInNonsimpleFinal =
      accumArray (\_ _ -> True) False (0, qcount - 1) $
        nonsimpleFinal'
          ^.. folded . \add -> (`freeModChilds` pure) $ \rec ->
            BTerm.modChilds
              BTerm.ChildMod
                { BTerm.lP = \p -> p <$ add (p, ())
                , BTerm.lT = rec
                }

    extendedStates
      | and simpleNonfinal && isNothing nonsimpleFinal = [0 .. qcount - 1] <&> Free . MTerm.State
      | otherwise =
        [0 .. qcount - 1] <&> \i ->
          case (simpleNonfinal ! i, qsInNonsimpleFinal ! i) of
            (True, _) ->
              Free $
                MTerm.And $
                  Free (MTerm.State i) :| [Free $ MTerm.Predicate $ Pure 3]
            (_, False) ->
              Free $
                MTerm.Or $
                  Free (MTerm.State i) :| [Free $ MTerm.Predicate $ Pure 2]
            _ ->
              Free $
                MTerm.Or $
                  Free (MTerm.State i)
                    :| [Free $ MTerm.Predicate $ Free $ BTerm.And $ Pure 2 :| [Free $ BTerm.Predicate i]]

    freeJust (Free t) = Just t
    freeJust _ = Nothing

    modPT lP lT = MTerm.modChilds MTerm.pureChildMod{MTerm.lT = lT, MTerm.lP = lP}

    flattenFree fn = either (return . Pure) $ return . Free . fn freeJust

    -- flattening highly improves performance
    states' =
      states <&> \x ->
        runIdentity $
          convertTransition x
            & cataT
              (freeTraversal $ modPT $ cataT (freeTraversal traversed) (flattenFree BTerm.flatten0))
              (flattenFree MTerm.flatten0)

    (fIxMap, fbterms, fmterms) = convertFormulae formulae fcount qcount acount

    convertTransition = (asRight .) $
      cataRecursive $ \case
        STrue -> Left $ Pure 0
        SFalse -> Left $ Pure 1
        SState q -> Right $ Pure q
        SFormula f -> case fIxMap ! f of
          (False, f) -> Left $ Pure f
          (True, f) -> Right $ Pure f
        SVar v -> Left $ Pure (v + 4)
        SNot (Left x) -> Left $ Free $ BTerm.Not x
        SAnd (Left x) (Left y) -> Left $ Free $ BTerm.And $ x :| [y]
        SOr (Left x) (Left y) -> Left $ Free $ BTerm.Or $ x :| [y]
        SAnd x y -> Right $ Free $ MTerm.And $ NE.map asRight $ x :| [y]
        SOr x y -> Right $ Free $ MTerm.Or $ NE.map asRight $ x :| [y]
        x -> error $ "non-exhaustive patterns " ++ show x

    init' = convertTransition init >>= Free . MTerm.State

    (init'', states'') = case nonsimpleFinal'' of
      Just finalTrans ->
        ( qcount
        , listArray (0, qcount + 1) $
            states'
              ++ [Free $ MTerm.And $ init' :| [Free $ MTerm.State $ qcount + 1], finalTrans]
        )
      Nothing -> case init' of
        Free (MTerm.State q) -> (q, listArray (0, qcount - 1) states')
        _ -> (qcount, listArray (0, qcount) $ states' ++ [init'])

finalSplitSimple :: Int -> Fix STerm' -> (Array Int Bool, Maybe (Fix (Compose [] STerm')))
finalSplitSimple qcount final =
  getSimples &&& getNonsimples $
    ($ final) $
      cataRecursive $ \case
        SState q -> Left (q, False)
        SNot (Left (q, False)) -> Left (q, True)
        SNot (Left (q, True)) -> Left (q, False)
        SNot x -> Right ([], Compose [SNot $ Fix $ Compose $ unsimplify2 x])
        SAnd (Left (q1, True)) (Left (q2, True)) -> Right ([q1, q2], Compose [])
        SAnd (Left (q1, True)) (Right (qs, nonSimples)) -> Right (q1 : qs, nonSimples)
        SAnd (Right (qs, nonSimples)) (Left (q2, True)) -> Right (q2 : qs, nonSimples)
        SAnd (Right (qs1, Compose nonSimples1)) (Right (qs2, Compose nonSimples2)) ->
          Right (qs1 ++ qs2, Compose $ nonSimples1 ++ nonSimples2)
        SAnd a (Right (qs, Compose nonSimples)) ->
          Right (qs, Compose $ unsimplify2 a ++ nonSimples)
        SAnd (Right (qs, Compose nonSimples)) b ->
          Right (qs, Compose $ unsimplify2 b ++ nonSimples)
        SAnd a b ->
          Right
            ( []
            , Compose
                [SAnd (Fix $ Compose $ unsimplify2 a) (Fix $ Compose $ unsimplify2 b)]
            )
        STrue -> Right ([], Compose [])
        SFalse -> Right ([], Compose [SFalse])
        SOr a b ->
          Right
            ( []
            , Compose
                [SOr (Fix $ Compose $ unsimplify2 a) (Fix $ Compose $ unsimplify2 b)]
            )
        x -> error $ "non-exhaustive patterns " ++ show x
  where
    qmask = accumArray (\_ _ -> True) False (0, qcount - 1)
    getSimples (Left (q, True)) = qmask [(q, ())]
    getSimples (Right (qs, _)) = qmask $ map (,()) qs
    getSimples x = error $ "non-exhaustive patterns " ++ show x

    getNonsimples (Left (q, True)) = Nothing
    getNonsimples (Right (_, Compose [])) = Nothing
    getNonsimples (Right (_, nonSimples)) = Just $ Fix nonSimples
    getNonsimples x = error $ "non-exhaustive patterns " ++ show x

    unsimplify q = SNot $ Fix $ Compose [SState q]

    unsimplify2 (Left (q, False)) = [SState q]
    unsimplify2 (Left (q, True)) = [SNot $ Fix $ Compose [SState q]]
    unsimplify2 (Right (qs, Compose nonSimples)) = map unsimplify qs ++ nonSimples

formatAfa :: BoolAfaUnswallowed Int -> T.Text
formatAfa (swallow -> BoolAfa bterms (Afa mterms states init)) =
  T.unlines $
    [ [i|@kInitialFormula: s#{init}|]
    , let finals = map (\q -> [i|!s#{q}|]) $ Data.Array.indices states
       in [i|@kFinalFormula: #{T.intercalate " & " finals}|]
    ]
      ++ map (\(j, t) -> [i|@fBool#{j}: #{fromBTermTree t}|]) (assocs bterms)
      ++ map (\(j, t) -> [i|@fMix#{j}: #{fromMTermTree t}|]) (assocs mterms)
      ++ map (\(j, t) -> [i|@s#{j}: #{fromMTermTree t}|]) (assocs states)

fromBTermTree :: BoolTermIFree Int -> T.Text
fromBTermTree = iter fromBTerm . fmap (\j -> [i|fBool#{j}|])

fromBTerm :: BTerm.Term Int T.Text -> T.Text
fromBTerm BTerm.LTrue = "kTrue"
fromBTerm BTerm.LFalse = "kFalse"
fromBTerm (BTerm.Predicate p) = [i|a#{p}|]
fromBTerm (BTerm.Not x) = [i|!#{x}|]
fromBTerm (BTerm.And (x :| [])) = x
fromBTerm (BTerm.Or (x :| [])) = x
fromBTerm (BTerm.And xs) = [i|(#{T.intercalate " & "$ NE.toList xs})|]
fromBTerm (BTerm.Or xs) = [i|(#{T.intercalate " | "$ NE.toList xs})|]

fromMTermTree :: MixTermIFree (BoolTermIFree Int) -> T.Text
fromMTermTree = iter fromMTerm . fmap (\j -> [i|fMix#{j}|])

fromMTerm :: MTerm.Term (BoolTermIFree Int) Int T.Text -> T.Text
fromMTerm MTerm.LTrue = "kTrue"
fromMTerm (MTerm.Predicate p) = fromBTermTree p
fromMTerm (MTerm.State q) = [i|s#{q}|]
fromMTerm (MTerm.And (x :| [])) = x
fromMTerm (MTerm.Or (x :| [])) = x
fromMTerm (MTerm.And xs) = [i|(#{T.intercalate " & "$ NE.toList xs})|]
fromMTerm (MTerm.Or xs) = [i|(#{T.intercalate " | "$ NE.toList xs})|]

----------------------------------------------------------------------------------------
-- STerm and its plate (boilerplate) ---------------------------------------------------

data STerm q f v r
  = STrue
  | SFalse
  | SState !q
  | SFormula !f
  | SVar !v
  | SNot !r
  | SAnd !r !r
  | SOr !r !r
  deriving (Functor, Foldable, Traversable, Show, Eq, Generic, Generic1)
  deriving (Eq1, Show1) via (Generically1 (STerm q f v))

-- MFun --------------------------------------------------------------------------------

data MFun q f v r q' f' v' r' = MFun
  { mfunSTrue :: forall q' f' v' r'. STerm q' f' v' r'
  , mfunSFalse :: forall q' f' v' r'. STerm q' f' v' r'
  , mfunSState :: forall f' v' r'. q -> STerm q' f' v' r'
  , mfunSFormula :: forall q' v' r'. f -> STerm q' f' v' r'
  , mfunSVar :: forall q' f' r'. v -> STerm q' f' v' r'
  , mfunSNot :: forall q' f' v'. r -> STerm q' f' v' r'
  , mfunSAnd :: forall q' f' v'. r -> r -> STerm q' f' v' r'
  , mfunSOr :: forall q' f' v'. r -> r -> STerm q' f' v' r'
  }

{-# INLINE mfun0 #-}
mfun0 :: MFun q f v r q f v r
mfun0 =
  MFun
    { mfunSTrue = STrue
    , mfunSFalse = SFalse
    , mfunSState = SState
    , mfunSFormula = SFormula
    , mfunSVar = SVar
    , mfunSNot = SNot
    , mfunSAnd = SAnd
    , mfunSOr = SOr
    }

{-# INLINE appMFun #-}
appMFun :: MFun q f v r q' f' v' r' -> STerm q f v r -> STerm q' f' v' r'
appMFun MFun{..} = \case
  STrue -> mfunSTrue
  SFalse -> mfunSFalse
  SState q -> mfunSState q
  SFormula f -> mfunSFormula f
  SVar v -> mfunSVar v
  SNot r -> mfunSNot r
  SAnd r1 r2 -> mfunSAnd r1 r2
  SOr r1 r2 -> mfunSOr r1 r2

data MTFun q f v r q' f' v' r' = MTFun
  { mtfunQ :: q -> q'
  , mtfunF :: f -> f'
  , mtfunV :: v -> v'
  , mtfunR :: r -> r'
  }

{-# INLINE mtfun0 #-}
mtfun0 :: MTFun q f v r q f v r
mtfun0 = MTFun id id id id

{-# INLINE fromMTFun #-}
fromMTFun :: MTFun q f v r q' f' v' r' -> MFun q f v r q' f' v' r'
fromMTFun MTFun{..} =
  mfun0
    { mfunSState = SState . mtfunQ
    , mfunSFormula = SFormula . mtfunF
    , mfunSVar = SVar . mtfunV
    , mfunSNot = SNot . mtfunR
    , mfunSAnd = \r1 r2 -> SAnd (mtfunR r1) (mtfunR r2)
    , mfunSOr = \r1 r2 -> SOr (mtfunR r1) (mtfunR r2)
    }

{-# INLINE appMTFun #-}
appMTFun :: MTFun q f v r q' f' v' r' -> STerm q f v r -> STerm q' f' v' r'
appMTFun = appMFun . fromMTFun

-- MFol --------------------------------------------------------------------------------

data MFol q f v r m = MFol
  { mfolSTrue :: m
  , mfolSFalse :: m
  , mfolSState :: q -> m
  , mfolSFormula :: f -> m
  , mfolSVar :: v -> m
  , mfolSNot :: r -> m
  , mfolSAnd :: r -> r -> m
  , mfolSOr :: r -> r -> m
  }

{-# INLINE mfol0 #-}
mfol0 :: Monoid m => MFol q f v r m
mfol0 =
  MFol
    { mfolSTrue = mempty
    , mfolSFalse = mempty
    , mfolSState = const mempty
    , mfolSFormula = const mempty
    , mfolSVar = const mempty
    , mfolSNot = const mempty
    , mfolSAnd = \_ _ -> mempty
    , mfolSOr = \_ _ -> mempty
    }

{-# INLINE appMFol #-}
appMFol :: MFol q f v r m -> STerm q f v r -> m
appMFol MFol{..} = \case
  STrue -> mfolSTrue
  SFalse -> mfolSFalse
  SState q -> mfolSState q
  SFormula f -> mfolSFormula f
  SVar v -> mfolSVar v
  SNot r -> mfolSNot r
  SAnd r1 r2 -> mfolSAnd r1 r2
  SOr r1 r2 -> mfolSOr r1 r2

data MTFol q f v r m = MTFol
  { mtfolQ :: q -> m
  , mtfolF :: f -> m
  , mtfolV :: v -> m
  , mtfolR :: r -> m
  }

{-# INLINE mtfol0 #-}
mtfol0 :: Monoid m => MTFol q f v r m
mtfol0 = MTFol (const mempty) (const mempty) (const mempty) (const mempty)

{-# INLINE fromMTFol #-}
fromMTFol :: Monoid m => MTFol q f v r m -> MFol q f v r m
fromMTFol MTFol{..} =
  mfol0
    { mfolSState = mtfolQ
    , mfolSFormula = mtfolF
    , mfolSVar = mtfolV
    , mfolSNot = mtfolR
    , mfolSAnd = \r1 r2 -> mtfolR r1 <> mtfolR r2
    , mfolSOr = \r1 r2 -> mtfolR r1 <> mtfolR r2
    }

{-# INLINE appMTFol #-}
appMTFol :: Monoid m => MTFol q f v r m -> STerm q f v r -> m
appMTFol = appMFol . fromMTFol

-- MTra --------------------------------------------------------------------------------

data MTra q f v r q' f' v' r' m = MTra
  { mtraSTrue :: forall q' f' v' r'. m (STerm q' f' v' r')
  , mtraSFalse :: forall q' f' v' r'. m (STerm q' f' v' r')
  , mtraSState :: forall f' v' r'. q -> m (STerm q' f' v' r')
  , mtraSFormula :: forall q' v' r'. f -> m (STerm q' f' v' r')
  , mtraSVar :: forall q' f' r'. v -> m (STerm q' f' v' r')
  , mtraSNot :: forall q' f' v'. r -> m (STerm q' f' v' r')
  , mtraSAnd :: forall q' f' v'. r -> r -> m (STerm q' f' v' r')
  , mtraSOr :: forall q' f' v'. r -> r -> m (STerm q' f' v' r')
  }

{-# INLINE mtra0 #-}
mtra0 :: Applicative m => MTra q f v r q f v r m
mtra0 =
  MTra
    { mtraSTrue = pure STrue
    , mtraSFalse = pure SFalse
    , mtraSState = pure . SState
    , mtraSFormula = pure . SFormula
    , mtraSVar = pure . SVar
    , mtraSNot = pure . SNot
    , mtraSAnd = pure .: SAnd
    , mtraSOr = pure .: SOr
    }

{-# INLINE appMTra #-}
appMTra :: MTra q f v r q' f' v' r' m -> STerm q f v r -> m (STerm q' f' v' r')
appMTra MTra{..} = \case
  STrue -> mtraSTrue
  SFalse -> mtraSFalse
  SState q -> mtraSState q
  SFormula f -> mtraSFormula f
  SVar v -> mtraSVar v
  SNot r -> mtraSNot r
  SAnd r1 r2 -> mtraSAnd r1 r2
  SOr r1 r2 -> mtraSOr r1 r2

data MTTra q f v r q' f' v' r' m = MTTra
  { mttraQ :: q -> m q'
  , mttraF :: f -> m f'
  , mttraV :: v -> m v'
  , mttraR :: r -> m r'
  }

{-# INLINE mttra0 #-}
mttra0 :: Applicative m => MTTra q f v r q f v r m
mttra0 = MTTra pure pure pure pure

{-# INLINE fromMTTra #-}
fromMTTra :: Applicative m => MTTra q f v r q' f' v' r' m -> MTra q f v r q' f' v' r' m
fromMTTra MTTra{..} =
  mtra0
    { mtraSState = fmap SState . mttraQ
    , mtraSFormula = fmap SFormula . mttraF
    , mtraSVar = fmap SVar . mttraV
    , mtraSNot = fmap SNot . mttraR
    , mtraSAnd = \r1 r2 -> SAnd <$> mttraR r1 <*> mttraR r2
    , mtraSOr = \r1 r2 -> SOr <$> mttraR r1 <*> mttraR r2
    }

{-# INLINE appMTTra #-}
appMTTra ::
  forall m q f v r q' f' v' r'.
  Applicative m =>
  MTTra q f v r q' f' v' r' m ->
  STerm q f v r ->
  m (STerm q' f' v' r')
appMTTra = appMTra . fromMTTra

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
