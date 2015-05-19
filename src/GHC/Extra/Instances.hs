{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

* 'Eq' instance for 'Ct'

* 'Ord' instance for 'Type' and 'Ct'
-}
module GHC.Extra.Instances where

import Data.Function (on)

import TcRnTypes     (Ct,ctPred)
import Type          (Type,cmpType)

instance Ord Type where
  compare = cmpType

instance Eq Ct where
  (==) = (==) `on` ctPred

instance Ord Ct where
  compare = compare `on` ctPred
