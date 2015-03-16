{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators  #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

import GHC.TypeLits

data Vec :: Nat -> * -> * where
  Nil  :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (n + 1) a

infixr 5 :>

tail :: Vec (n + 1) a -> Vec n a
tail (_ :> xs) = xs
