{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

* 'Eq' instance for 'Ct'

* 'Ord' instance for 'Type' and 'Ct'
-}

{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module GHC.Extra.Instances where

import Type (Type,cmpType)
#if __GLASGOW_HASKELL__ >= 711
import Type (eqType)
#endif

#if __GLASGOW_HASKELL__ >= 711
instance Eq Type where
  (==) = eqType
#endif

instance Ord Type where
  compare = cmpType
