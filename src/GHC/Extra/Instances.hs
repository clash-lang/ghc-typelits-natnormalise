{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

* 'Eq' instance for 'Ct'

* 'Ord' instance for 'Type' and 'Ct'
-}
module GHC.Extra.Instances where

import Type          (Type,cmpType)

instance Ord Type where
  compare = cmpType
