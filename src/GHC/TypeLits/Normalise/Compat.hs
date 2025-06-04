
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module GHC.TypeLits.Normalise.Compat
  ( LookedUpTyCons(..), lookupTyCons
  , mkLEqNat
  , Relation, isNatRel
  ) where

-- base
import GHC.TypeNats
  ( CmpNat )
#if MIN_VERSION_ghc(9,2,0)
import qualified Data.Type.Ord
  ( OrdCond, type (<=) )
import qualified GHC.TypeError
  ( Assert )
#else
import GHC.TypeNats
  ( type (<=), type (<=?) )
#endif

-- ghc
import GHC.Builtin.Types
  ( isCTupleTyConName
  , promotedFalseDataCon, promotedTrueDataCon
  , promotedLTDataCon, promotedEQDataCon, promotedGTDataCon
  )
#if MIN_VERSION_ghc(9,1,0)
import GHC.Builtin.Types
  ( cTupleTyCon, cTupleDataCon )
#else
import GHC.Builtin.Types
  ( cTupleTyConName, cTupleDataConName )
#endif

-- ghc-tcplugin-api
import GHC.TcPlugin.API

--------------------------------------------------------------------------------

data LookedUpTyCons
  = LookedUpTyCons
    {
#if MIN_VERSION_ghc(9,1,0)
      ordCondTyCon :: TyCon
    , assertTyCon :: TyCon
       -- | @<= :: k -> k -> Constraint@
    , leqTyCon :: TyCon
#else
      -- | @<= :: Nat -> Nat -> Constraint@
      leqNatTyCon :: TyCon
      -- | @<=? :: Nat -> Nat -> Constraint@
    , leqQNatTyCon :: TyCon
#endif
    , cmpNatTyCon :: TyCon
    , c0TyCon   :: TyCon
    , c0DataCon :: DataCon
    }

lookupTyCons :: TcPluginM Init LookedUpTyCons
lookupTyCons = do
    cmpNatT <- lookupTHName ''GHC.TypeNats.CmpNat >>= tcLookupTyCon
#if MIN_VERSION_ghc(9,1,0)
    leqT    <- lookupTHName ''(Data.Type.Ord.<=) >>= tcLookupTyCon
    ordCond <- lookupTHName ''Data.Type.Ord.OrdCond >>= tcLookupTyCon
    assertT <- lookupTHName ''GHC.TypeError.Assert >>= tcLookupTyCon
    return $
      LookedUpTyCons
        { leqTyCon     = leqT
        , ordCondTyCon = ordCond
        , assertTyCon  = assertT
        , cmpNatTyCon  = cmpNatT
        , c0TyCon      = cTupleTyCon 0
        , c0DataCon    = cTupleDataCon 0
        }
#else
    leqNatT <- lookupTHName ''(GHC.TypeNats.<=) >>= tcLookupTyCon
    leqQT   <- lookupTHName ''(GHC.TypeNats.<=?) >>= tcLookupTyCon
    c0T <- tcLookupTyCon (cTupleTyConName 0)
    c0D <- tcLookupDataCon (cTupleDataConName 0)
    return $
      LookedUpTyCons
        { leqNatTyCon  = leqNatT
        , leqQNatTyCon = leqQT
        , c0TyCon      = c0T
        , c0DataCon    = c0D
        , cmpNatTyCon  = cmpNatT
        }
#endif

-- | The constraint @a <= b@.
mkLEqNat :: LookedUpTyCons -> Type -> Type -> PredType
mkLEqNat tcs a b =
#if MIN_VERSION_ghc(9,1,0)
    mkTyConApp (leqTyCon tcs) [natKind,a,b]
#else
    mkTyConApp (leqNatTyCon tcs) [a,b]
#endif

-- | Is this type 'True' or 'False'?
boolean_maybe :: Type -> Maybe Bool
boolean_maybe ty
  | Just (tc, []) <- splitTyConApp_maybe ty
  = if | tc == promotedTrueDataCon
       -> Just True
       | tc == promotedFalseDataCon
       -> Just False
       | otherwise
       -> Nothing
  | otherwise
  = Nothing

-- | Is this type 'LT', 'EQ' or 'GT'?
ordering_maybe :: Type -> Maybe Ordering
ordering_maybe ty
  | Just (tc, []) <- splitTyConApp_maybe ty
  = if | tc == promotedLTDataCon
       -> Just LT
       | tc == promotedEQDataCon
       -> Just EQ
       | tc == promotedGTDataCon
       -> Just GT
       | otherwise
       -> Nothing
  | otherwise
  = Nothing

-- | Is this type @() :: Constraint@?
isUnitCTuple :: PredType -> Bool
isUnitCTuple pty
  | Just (tc, []) <- splitTyConApp_maybe pty
  = isCTupleTyConName (tyConName tc)
  | otherwise
  = False

-- | A relation between two natural numbers, @((x,y), mbRel)@.
--
-- The @mbRel@ value indicates the kind of relation:
--
--  - @Nothing@ <=> @x ~ y@,
--  - @Just b@ <=> @(x <=? y) ~ b@.
type Relation = ((Type, Type), Maybe Bool)

{- Note [Recognising Nat inequalities]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Recognising whether a type is an inequality between two natural numbers is
not as straightforward as one might initially think. The problem is that there
are many different built-in types that can be used to represent an equality of
natural numbers:

  1. GHC.TypeNats.CmpNat, returning Ordering.
     This type family is primitive (on all GHC versions).
  2. GHC.TypeNats.<=?, returning a Boolean.
     This type family is primitive prior to GHC 9.1, but is defined in
     terms of the 'OrdCond' type family starting in GHC 9.1.

     (NB: it also becomes poly-kinded starting in GHC 9.1.)
  3. GHC.TypeNats.<=, which is defined:
    (a) as @x <= y@ <=> @(x <=? y) ~ True@ in GHC prior to 9.1.
    (b) as @Assert (x <=? y) ...@ in GHC 9.1 and above.

To catch all of these, we must thus handle all of the following type families:

  Case 1. CmpNat.
  Case 2. (<=?) in GHC 9.1 and prior.
  Case 3. OrdCond in GHC 9.1 and later.
  Case 4. Assert, in GHC 9.1 and later.

These are all the built-in type families defined in GHC used to express
inequalities between natural numbers.
-}

-- | Is this an equality or inequality between two natural numbers?
--
-- See Note [Recognising Nat inequalities].
isNatRel :: LookedUpTyCons -> PredType -> Maybe Relation
isNatRel tcs ty0
  | EqPred NomEq x y <- classifyPredType ty0
  = if
      -- (b :: Bool) ~ y
      | Just b <- boolean_maybe x
      -> booleanRel b y
      -- x ~ (b :: Bool)
      | Just b <- boolean_maybe y
      -> booleanRel b x
      | Just o <- ordering_maybe x
      -- (o :: Ordering) ~ y
      -> orderingRel o y
      | Just o <- ordering_maybe y
      -- x ~ (o :: Ordering)
      -> orderingRel o x
      -- (() :: Constraint) ~ y
      | isUnitCTuple x
      -> goTy y
      -- x ~ (() :: Constraint)
      | isUnitCTuple y
      -> goTy x
      | otherwise
      -> Nothing
  | otherwise
  = goTy ty0
  where
    goTy :: PredType -> Maybe Relation
    goTy ty
      | Just (tc, tys) <- splitTyConApp_maybe ty
      = goTc tc tys
      | otherwise
      = Nothing

    goTc _tc _tys
#if MIN_VERSION_ghc(9,1,0)
      -- Look through 'Assert'.
      -- Case 4 in Note [Recognising Nat inequalities]
      | _tc == assertTyCon tcs
      , [ty, _] <- _tys
      = booleanRel True ty
#endif
      | otherwise
      = Nothing

    -- Recognise whether @(b :: Bool) ~ ty@ is an equality/inequality
    booleanRel :: Bool -> Type -> Maybe Relation
    booleanRel b ty =
      case splitTyConApp_maybe ty of
        Nothing -> Nothing
        Just (tc, tys)
#if MIN_VERSION_ghc(9,1,0)
          -- OrdCond (CmpNat x y) lt eq gt ~ b
          -- Case 3 in Note [Recognising Nat inequalities]
          | tc == ordCondTyCon tcs
          , [_,cmp,ltTy,eqTy,gtTy] <- tys
          , Just lt <- boolean_maybe ltTy
          , Just eq <- boolean_maybe eqTy
          , Just gt <- boolean_maybe gtTy
          , Just (tcCmpNat, [x,y]) <- splitTyConApp_maybe cmp
          , tcCmpNat == cmpNatTyCon tcs
          -> if -- (x <= y) ~ b
                | lt && eq && not gt
                -> Just ((x,y), Just b)
                -- (x < y) ~ b
                --   <=>
                -- (y <= x) ~ not b
                | lt && not eq && not gt
                -> Just ((y,x), Just $ not b)
                -- (x >= y) ~ b
                --  <=>
                -- (y <= x) ~ b
                | not lt && eq && gt
                -> Just ((y,x), Just b)
                -- (x > y) ~ b
                --   <=>
                -- (x <= y) ~ not b
                | not lt && not eq && gt
                -> Just ((x,y), Just $ not b)
                -- x ~ y
                |  ( b && not lt && eq && not gt )
                || ( not b && lt && not eq && gt )
                -> Just ((x,y), Nothing)
                | otherwise
                -> Nothing
#else
          -- (x <=? y) ~ b
          -- Case 2 in Note [Recognising Nat inequalities]
          | tc == leqQNatTyCon tcs
          , [x,y] <- tys
          -> Just ((x,y), Just b)
#endif
          | otherwise
          -> Nothing

    -- Recognise whether @(o :: Ordering) ~ ty@ is an equality/inequality
    orderingRel :: Ordering -> Type -> Maybe Relation
    orderingRel o ty =
      case splitTyConApp_maybe ty of
        Nothing -> Nothing
        Just (tc, tys)
          -- CmpNat x y ~ o
          -- Case 1 in Note [Recognising Nat inequalities]
          | tc == cmpNatTyCon tcs
          , [x,y] <- tys
          ->
            case o of
              EQ ->
                -- x ~ y
                Just ((x,y), Nothing)
              LT ->
                -- x < y  <=>  (y <= x) ~ False
                Just ((y,x), Just False)
              GT ->
                -- x > y  <=>  (x <= y) ~ False
                Just ((x,y), Just False)
          | otherwise
          -> Nothing
