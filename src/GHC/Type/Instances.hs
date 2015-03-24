{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

Ord instance for 'Type'
-}
module GHC.Type.Instances where

import Type (Type,cmpType)

instance Ord Type where
  compare = cmpType
