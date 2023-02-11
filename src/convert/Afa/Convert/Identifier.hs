{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Afa.Convert.Identifier where

import qualified Afa.Lib as Lib
import qualified Afa.RemoveFinals as RmF
import Data.String.Interpolate.IsString (i)
import qualified Data.Text as T
import Data.Word

class Identify a where
  identify :: a -> T.Text

instance Identify T.Text where
  identify = id

instance Identify Word32 where
  identify = T.pack . show

instance Identify Word8 where
  identify = T.pack . show

instance Identify q => Identify (Lib.AddOneQ q) where
  identify Lib.AddedQ = "I"
  identify (Lib.OriginalQ q) = [i|O#{identify q}|]

instance Identify q => Identify (Lib.QomboQ q) where
  identify (Lib.QomboQ j q) = [i|#{j}_#{identify q}|]

instance (Identify q, Identify v) => Identify (RmF.SyncVar q v) where
  identify (RmF.VVar v) = [i|V#{identify v}|]
  identify RmF.FVar = "F"
  identify (RmF.QVar q) = [i|Q#{identify q}|]
