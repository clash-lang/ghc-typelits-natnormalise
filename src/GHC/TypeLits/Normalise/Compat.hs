
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module GHC.TypeLits.Normalise.Compat
  ( LookedUpTyCons(..), lookupTyCons
  , upToGivens
  , mkLEqNat
  , Relation, isNatRel

  , UniqMap, intersectUniqMap_C, listToUniqMap, nonDetUniqMapToList

  ) where

-- base
import Control.Arrow
  ( second )
import qualified Data.List.NonEmpty as NE
  ( toList )
import Data.Foldable
  ( asum )
import GHC.TypeNats
  ( CmpNat )
#if MIN_VERSION_ghc(9,3,0)
import qualified GHC.TypeError
  ( Assert )
#endif
#if MIN_VERSION_ghc(9,1,0)
import qualified Data.Type.Ord
  ( OrdCond, type (<=) )

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
  ( cTupleTyConName )
#endif
#if MIN_VERSION_ghc(9,7,0)
import GHC.Types.Unique.Map
  ( UniqMap, intersectUniqMap_C, listToUniqMap, nonDetUniqMapToList )
#else
import GHC.Types.Unique
  ( Uniquable )
import GHC.Types.Unique.FM
  ( intersectUFM_C, nonDetEltsUFM )
#endif


-- ghc-tcplugin-api
import GHC.TcPlugin.API
import GHC.TcPlugin.API.TyConSubst
  ( TyConSubst, splitTyConApp_upTo )

--------------------------------------------------------------------------------

data LookedUpTyCons
  = LookedUpTyCons
    {
#if MIN_VERSION_ghc(9,3,0)
      assertTyCon :: TyCon,
#endif
#if MIN_VERSION_ghc(9,1,0)
       -- | @<= :: k -> k -> Constraint@
      ordCondTyCon :: TyCon,
      leqTyCon :: TyCon,
#else
       -- | @<= :: Nat -> Nat -> Constraint@
      leqNatTyCon :: TyCon,
      -- | @<=? :: Nat -> Nat -> Constraint@
      leqQNatTyCon :: TyCon,
#endif
      cmpNatTyCon :: TyCon,
      c0TyCon   :: TyCon,
      c0DataCon :: DataCon
    }

lookupTyCons :: TcPluginM Init LookedUpTyCons
lookupTyCons = do
    cmpNatT <- lookupTHName ''GHC.TypeNats.CmpNat >>= tcLookupTyCon
#if MIN_VERSION_ghc(9,3,0)
    assertT <- lookupTHName ''GHC.TypeError.Assert >>= tcLookupTyCon
#endif
#if MIN_VERSION_ghc(9,1,0)
    leqT    <- lookupTHName ''(Data.Type.Ord.<=) >>= tcLookupTyCon
    ordCond <- lookupTHName ''Data.Type.Ord.OrdCond >>= tcLookupTyCon
    return $
      LookedUpTyCons
        { leqTyCon     = leqT
        , ordCondTyCon = ordCond
#  if MIN_VERSION_ghc(9,3,0)
        , assertTyCon  = assertT
#  endif
        , cmpNatTyCon  = cmpNatT
        , c0TyCon      = cTupleTyCon 0
        , c0DataCon    = cTupleDataCon 0
        }
#else
    leqT  <- lookupTHName ''(GHC.TypeNats.<=)  >>= tcLookupTyCon
    leqQT <- lookupTHName ''(GHC.TypeNats.<=?) >>= tcLookupTyCon
    c0T   <- tcLookupTyCon (cTupleTyConName 0)
    let c0D = tyConSingleDataCon c0T
      -- somehow looking up the 0-tuple data constructor fails
      -- with interface file errors, so use tyConSingleDataCon
    return $
      LookedUpTyCons
        { leqNatTyCon  = leqT
        , leqQNatTyCon = leqQT
        , c0TyCon      = c0T
        , c0DataCon    = c0D
        , cmpNatTyCon  = cmpNatT
        }
#endif

-- | The constraint @(a <= b)@.
mkLEqNat :: LookedUpTyCons -> Type -> Type -> PredType
mkLEqNat tcs a b =
#if MIN_VERSION_ghc(9,3,0)
  -- Starting from GHC 9.3, (a <= b) turns into 'Assert (a <=? b) msg'.
  -- We prefer to emit 'Assert (a <=? b) msg ~ (() :: Constraint)',
  -- in order to avoid creating an Irred constraint.
  mkEqPredRole Nominal
    (mkTyConApp (leqTyCon tcs) [natKind, a, b])
    (mkTyConTy $ c0TyCon tcs)
#elif MIN_VERSION_ghc(9,1,0)
  mkTyConApp (leqTyCon tcs) [natKind, a, b]
#else
  mkTyConApp (leqNatTyCon tcs) [a, b]
#endif

-- | Is this type 'True' or 'False'?
boolean_maybe :: TyConSubst -> Type -> Maybe (Bool, [Coercion])
boolean_maybe givensTyConSubst =
  upToGivens givensTyConSubst ( \ tc tys -> (, []) <$> go tc tys )
  where
    go tc []
      | tc == promotedTrueDataCon
      = Just True
      | tc == promotedFalseDataCon
      = Just False
    go _ _ = Nothing

-- | Is this type 'LT', 'EQ' or 'GT'?
ordering_maybe :: TyConSubst -> Type -> Maybe (Ordering, [Coercion])
ordering_maybe givensTyConSubst =
  upToGivens givensTyConSubst ( \ tc tys -> (, []) <$> go tc tys )
  where
    go tc []
      | tc == promotedLTDataCon
      = Just LT
      | tc == promotedEQDataCon
      = Just EQ
      | tc == promotedGTDataCon
      = Just GT
    go _ _ = Nothing

#if MIN_VERSION_ghc(9,1,0)
cmpNat_maybe :: LookedUpTyCons -> TyConSubst -> Type -> Maybe ((Type, Type), [Coercion])
cmpNat_maybe tcs givensTyConSubst =
  upToGivens givensTyConSubst ( \ tc tys -> (, []) <$> go tc tys )
  where
    go tc [x,y]
      | tc == cmpNatTyCon tcs
      = Just (x,y)
    go _ _ = Nothing
#endif

-- | Is this type @() :: Constraint@?
unitCTuple_maybe :: TyConSubst -> PredType -> Maybe ((), [Coercion])
unitCTuple_maybe givensTyConSubst =
  upToGivens givensTyConSubst ( \ tc tys -> (, []) <$> go tc tys )
    where
      go tc []
        | isCTupleTyConName (tyConName tc)
        = Just ()
      go _ _ = Nothing

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
    (a) as @x <= y@ <=> @(x <=? y) ~ True@ in GHC prior to 9.3.
    (b) as @Assert (x <=? y) ...@ in GHC 9.3 and above.

To catch all of these, we must thus handle all of the following type families:

  Case 1. CmpNat.
  Case 2. (<=?) in GHC 9.1 and prior.
  Case 3. OrdCond in GHC 9.1 and later.
  Case 4. Assert, in GHC 9.3 and later.

These are all the built-in type families defined in GHC used to express
inequalities between natural numbers.
-}

-- | Is this an equality or inequality between two natural numbers?
--
-- See Note [Recognising Nat inequalities].
isNatRel :: LookedUpTyCons -> TyConSubst -> PredType -> Maybe (Relation, [Coercion])
isNatRel tcs givensTyConSubst ty0
  | EqPred NomEq x y <- classifyPredType ty0
  = if
      -- (b :: Bool) ~ y
      | Just ( b, cos1 ) <- boolean_maybe givensTyConSubst x
      -> second ( ++ cos1 ) <$> booleanRel b y
      -- x ~ (b :: Bool)
      | Just ( b, cos1 ) <- boolean_maybe givensTyConSubst y
      -> second ( ++ cos1 ) <$> booleanRel b x
      | Just ( o, cos1 ) <- ordering_maybe givensTyConSubst x
      -- (o :: Ordering) ~ y
      -> second ( ++ cos1 ) <$> orderingRel o y
      | Just ( o, cos1 ) <- ordering_maybe givensTyConSubst y
      -- x ~ (o :: Ordering)
      -> second ( ++ cos1 ) <$> orderingRel o x
      -- (() :: Constraint) ~ y
      | Just ( (), cos1 ) <- unitCTuple_maybe givensTyConSubst x
      -> second ( ++ cos1 ) <$> goTy y
      -- x ~ (() :: Constraint)
      | Just ( (), cos1 ) <- unitCTuple_maybe givensTyConSubst y
      -> second ( ++ cos1 ) <$> goTy x
      | otherwise
      -> Nothing
  | otherwise
  = goTy ty0
  where
    goTy :: PredType -> Maybe (Relation, [Coercion])
    goTy = upToGivens givensTyConSubst goTc

    goTc :: TyCon -> [Type] -> Maybe (Relation, [Coercion])
    goTc _tc _tys
#if MIN_VERSION_ghc(9,3,0)
      -- Look through 'Assert'.
      -- Case 4 in Note [Recognising Nat inequalities]
      | _tc == assertTyCon tcs
      , [ty, _] <- _tys
      = booleanRel True ty
#endif
      | otherwise
      = Nothing

    -- Recognise whether @(b :: Bool) ~ ty@ is an equality/inequality
    booleanRel :: Bool -> Type -> Maybe (Relation, [Coercion])
    booleanRel b = upToGivens givensTyConSubst (goBoolean b)

    goBoolean :: Bool -> TyCon -> [Type] -> Maybe (Relation, [Coercion])
    goBoolean b tc tys
#if MIN_VERSION_ghc(9,1,0)
      -- OrdCond (CmpNat x y) lt eq gt ~ b
      -- Case 3 in Note [Recognising Nat inequalities]
      | tc == ordCondTyCon tcs
      , [_,cmp,ltTy,eqTy,gtTy] <- tys
      , Just (lt, cos1) <- boolean_maybe givensTyConSubst ltTy
      , Just (eq, cos2) <- boolean_maybe givensTyConSubst eqTy
      , Just (gt, cos3) <- boolean_maybe givensTyConSubst gtTy
      , Just ((x,y), cos4) <- cmpNat_maybe tcs givensTyConSubst cmp
      = ( , cos1 ++ cos2 ++ cos3 ++ cos4 ) <$>
        if -- (x <= y) ~ b
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
      = Just (((x,y), Just b), [])
#endif
      | otherwise
      = Nothing

    -- Recognise whether @(o :: Ordering) ~ ty@ is an equality/inequality
    orderingRel :: Ordering -> Type -> Maybe (Relation, [Coercion])
    orderingRel o = upToGivens givensTyConSubst (goOrdering o)

    goOrdering :: Ordering -> TyCon -> [Type] -> Maybe (Relation, [Coercion])
    goOrdering o tc tys
      -- CmpNat x y ~ o
      -- Case 1 in Note [Recognising Nat inequalities]
      | tc == cmpNatTyCon tcs
      , [x,y] <- tys
      = ( , [] ) <$>
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
      = Nothing

upToGivens :: TyConSubst -> (TyCon -> [Type] -> Maybe (a, [Coercion])) -> Type -> Maybe (a, [Coercion])
upToGivens givensTyConSubst f ty =
  asum $ map ( \ (tc, tys, deps) -> second ( deps ++ ) <$> f tc tys ) $
    maybe [] NE.toList $ splitTyConApp_upTo givensTyConSubst ty

--------------------------------------------------------------------------------
#if !MIN_VERSION_ghc(9,7,0)

newtype UniqMap k a = UniqMap ( UniqFM k (k, a) )
    deriving (Eq, Functor)
type role UniqMap nominal representational

intersectUniqMap_C :: (a -> b -> c) -> UniqMap k a -> UniqMap k b -> UniqMap k c
intersectUniqMap_C f (UniqMap m1) (UniqMap m2) = UniqMap $ intersectUFM_C (\(k, a) (_, b) -> (k, f a b)) m1 m2
{-# INLINE intersectUniqMap_C #-}

listToUniqMap :: Uniquable k => [(k,a)] -> UniqMap k a
listToUniqMap kvs = UniqMap (listToUFM [ (k,(k,v)) | (k,v) <- kvs])
{-# INLINE listToUniqMap #-}

nonDetUniqMapToList :: UniqMap k a -> [(k, a)]
nonDetUniqMapToList (UniqMap m) = nonDetEltsUFM m
{-# INLINE nonDetUniqMapToList #-}

#endif
