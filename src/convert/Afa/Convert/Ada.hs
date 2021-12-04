{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Afa.Convert.Ada where

import Control.Lens
import Control.RecursionSchemes.Lens
import Data.Array
import qualified Data.List.NonEmpty as NE
import Data.String.Interpolate.IsString
import qualified Data.Text as T

import Afa
import Afa.Bool
import qualified Afa.Convert.Capnp.Afa as CapAfa (varCount)
import qualified Afa.Term.Bool as BTerm
import qualified Afa.Term.Mix as MTerm

toAda :: BoolAfaUnswallowed Int -> T.Text
toAda (BoolAfa bterms (Afa mterms states init)) =
  T.unlines
    [ "STATES"
    , T.unwords $ map (\j -> [i|q#{j}|]) [0 .. qcount]
    , ""
    , "INITIAL"
    , [i|q#{init}|]
    , ""
    , "FINAL"
    , [i|q#{qcount}|]
    , ""
    , "SYMBOLS"
    , "a"
    , ""
    , "VARIABLES"
    , T.unwords $ map (\j -> [i|v#{j}v|]) [0 .. max 0 (varCnt - 1)]
    , ""
    , "TRANSITIONS"
    , T.intercalate "\n" $
        flip map (assocs states) $ \(q, t) ->
          T.intercalate
            "\n"
            [ [i|a q#{q}|]
            , mtexts ! t
            , "#"
            ]
    ]
  where
    qcount = rangeSize $ bounds states
    (varCnt, bterms') = CapAfa.varCount bterms
    qDisj = T.intercalate " | " $ map (\q -> [i|q#{q}|]) [0 .. qcount - 1]

    btexts = bterms' & cataScan mapped %~ fromBTerm
    mtexts =
      mterms
        & cataScan
          ( sets $ \rec ->
              MTerm.appMTFun MTerm.mtfun0{MTerm.mtfunP = (btexts !), MTerm.mtfunT = rec}
          )
        %~ fromMTerm

fromBTerm :: BTerm.Term Int T.Text -> T.Text
fromBTerm BTerm.LTrue = "true"
fromBTerm BTerm.LFalse = "false"
fromBTerm (BTerm.Predicate p) = [i|(= v#{p}v1 0)|]
fromBTerm (BTerm.Not x) = [i|(not #{x})|]
fromBTerm (BTerm.And xs) = [i|(and #{T.intercalate " "$ NE.toList xs})|]
fromBTerm (BTerm.Or xs) = [i|(or #{T.intercalate " "$ NE.toList xs})|]

fromMTerm :: MTerm.Term T.Text Int T.Text -> T.Text
fromMTerm MTerm.LTrue = "true"
fromMTerm (MTerm.Predicate p) = p
fromMTerm (MTerm.State q) = [i|q#{q}|]
fromMTerm (MTerm.And xs) = [i|(and #{T.intercalate " "$ NE.toList xs})|]
fromMTerm (MTerm.Or xs) = [i|(or #{T.intercalate " "$ NE.toList xs})|]
