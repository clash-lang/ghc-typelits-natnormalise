{-|
Copyright  :  (C) 2015-2016, University of Twente,
                  2017     , QBayLogic B.V.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

A type checker plugin for GHC that can solve /equalities/ of types of kind
'GHC.TypeLits.Nat', where these types are either:

* Type-level naturals
* Type variables
* Applications of the arithmetic expressions @(+,-,*,^)@.

It solves these equalities by normalising them to /sort-of/
'GHC.TypeLits.Normalise.SOP.SOP' (Sum-of-Products) form, and then perform a
simple syntactic equality.

For example, this solver can prove the equality between:

@
(x + 2)^(y + 2)
@

and

@
4*x*(2 + x)^y + 4*(2 + x)^y + (2 + x)^y*x^2
@

Because the latter is actually the 'GHC.TypeLits.Normalise.SOP.SOP' normal form
of the former.

To use the plugin, add

@
{\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise \#-\}
@

To the header of your file.

== Treating subtraction as addition with a negated number

If you are absolutely sure that your subtractions can /never/ lead to (a locally)
negative number, you can ask the plugin to treat subtraction as addition with
a negated operand by additionally adding:

@
{\-\# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers \#-\}
@

to the header of your file, thereby allowing to use associativity and
commutativity rules when proving constraints involving subtractions. Note that
this option can lead to unsound behaviour and should be handled with extreme
care.

=== When it leads to unsound behaviour

For example, enabling the /allow-negated-numbers/ feature would allow
you to prove:

@
(n - 1) + 1 ~ n
@

/without/ a @(1 <= n)@ constraint, even though when /n/ is set to /0/ the
subtraction @n-1@ would be locally negative and hence not be a natural number.

This would allow the following erroneous definition:

@
data Fin (n :: Nat) where
  FZ :: Fin (n + 1)
  FS :: Fin n -> Fin (n + 1)

f :: forall n . Natural -> Fin n
f n = case of
  0 -> FZ
  x -> FS (f \@(n-1) (x - 1))

fs :: [Fin 0]
fs = f \<$\> [0..]
@

=== When it might be Okay

This example is taken from the <http://hackage.haskell.org/package/mezzo mezzo>
library.

When you have:

@
-- | Singleton type for the number of repetitions of an element.
data Times (n :: Nat) where
    T :: Times n

-- | An element of a "run-length encoded" vector, containing the value and
-- the number of repetitions
data Elem :: Type -> Nat -> Type where
    (:*) :: t -> Times n -> Elem t n

-- | A length-indexed vector, optimised for repetitions.
data OptVector :: Type -> Nat -> Type where
    End  :: OptVector t 0
    (:-) :: Elem t l -> OptVector t (n - l) -> OptVector t n
@

And you want to define:

@
-- | Append two optimised vectors.
type family (x :: OptVector t n) ++ (y :: OptVector t m) :: OptVector t (n + m) where
    ys        ++ End = ys
    End       ++ ys = ys
    (x :- xs) ++ ys = x :- (xs ++ ys)
@

then the last line will give rise to the constraint:

@
(n-l)+m ~ (n+m)-l
@

because:

@
x  :: Elem t l
xs :: OptVector t (n-l)
ys :: OptVector t m
@

In this case it's okay to add

@
{\-\# OPTIONS_GHC -fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers \#-\}
@

if you can convince yourself you will never be able to construct a:

@
xs :: OptVector t (n-l)
@

where /n-l/ is a negative number.
-}

{-# LANGUAGE CPP             #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE TupleSections   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Control.Arrow       (second)
import Control.Monad       ((<=<))
#if !MIN_VERSION_ghc(8,4,1)
import Control.Monad       (replicateM)
#endif
import Control.Monad.Trans.Writer.Strict
import Data.Either         (rights)
import Data.List           (intersect, stripPrefix)
import Data.Maybe          (mapMaybe)
import Data.Set            (Set, empty, toList)
import GHC.TcPluginM.Extra (tracePlugin)
import qualified GHC.TcPluginM.Extra as TcPluginM
#if MIN_VERSION_ghc(8,4,0)
import GHC.TcPluginM.Extra (flattenGivens)
#endif
import Text.Read           (readMaybe)

-- GHC API
#if MIN_VERSION_ghc(8,5,0)
import CoreSyn    (Expr (..))
#endif
import Outputable (Outputable (..), (<+>), ($$), text)
import Plugins    (Plugin (..), defaultPlugin)
#if MIN_VERSION_ghc(8,6,0)
import Plugins    (purePlugin)
#endif
import PrelNames  (knownNatClassName)
import TcEvidence (EvTerm (..))
#if !MIN_VERSION_ghc(8,4,0)
import TcPluginM  (zonkCt)
#endif
import TcPluginM  (TcPluginM, tcPluginTrace)
import TcRnTypes  (Ct, TcPlugin (..), TcPluginResult(..), ctEvidence, ctEvPred,
                   isWanted, mkNonCanonical)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType,
                   classifyPredType, eqType, getEqPredTys, mkTyVarTy)
import TysWiredIn (typeNatKind)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar, tcLookupClass)
import TcRnTypes
  (CtEvidence (..), CtLoc, TcEvDest (..), ctEvLoc, ctLoc, ctLocSpan, isGiven,
   setCtLoc, setCtLocSpan)
#if MIN_VERSION_ghc(8,2,0)
import TcRnTypes  (ShadowInfo (WDeriv))
#endif
import TyCoRep    (UnivCoProvenance (..))
import Type       (mkClassPred, mkPrimEqPred)
import TcType     (typeKind)
import TyCoRep    (Type (..))
import TcTypeNats (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                   typeNatSubTyCon)

import TcTypeNats (typeNatLeqTyCon)
import TysWiredIn (promotedFalseDataCon, promotedTrueDataCon)

-- internal
import GHC.TypeLits.Normalise.Unify

-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin
  = defaultPlugin
  { tcPlugin = fmap (normalisePlugin . foldr id defaultOpts) . traverse parseArgument
#if MIN_VERSION_ghc(8,6,0)
  , pluginRecompile = purePlugin
#endif
  }
 where
  parseArgument "allow-negated-numbers" = Just (\ opts -> opts { negNumbers = True })
  parseArgument (readMaybe <=< stripPrefix "depth=" -> Just depth) = Just (\ opts -> opts { depth })
  parseArgument _ = Nothing
  defaultOpts = Opts { negNumbers = False, depth = 5 }

data Opts = Opts { negNumbers :: Bool, depth :: Word }

normalisePlugin :: Opts -> TcPlugin
normalisePlugin opts = tracePlugin "ghc-typelits-natnormalise"
  TcPlugin { tcPluginInit  = return ()
           , tcPluginSolve = const (decideEqualSOP opts)
           , tcPluginStop  = const (return ())
           }

decideEqualSOP
  :: Opts
  -> [Ct]
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginResult
decideEqualSOP _opts _givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP opts  givens  _deriveds wanteds = do
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
    let wanteds' = filter (isWanted . ctEvidence) wanteds
    let unit_wanteds = mapMaybe toNatEquality wanteds'
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
#if MIN_VERSION_ghc(8,4,0)
        let unit_givens = mapMaybe toNatEquality (givens ++ flattenGivens givens)
#else
        unit_givens <- mapMaybe toNatEquality <$> mapM zonkCt givens
#endif
        sr <- simplifyNats opts unit_givens unit_wanteds
        tcPluginTrace "normalised" (ppr sr)
        case sr of
          Simplified evs -> do
            let solved = filter (isWanted . ctEvidence . (\((_,x),_) -> x)) evs
                (solved',newWanteds) = second concat (unzip solved)
            return (TcPluginOk solved' newWanteds)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality   = (Ct,CoreSOP,CoreSOP)
type NatInEquality = (Ct,(CoreSOP,CoreSOP,Bool))

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

data SimplifyResult
  = Simplified [((EvTerm,Ct),[Ct])]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats
  :: Opts
  -- ^ Allow negated numbers (potentially unsound!)
  -> [(Either NatEquality NatInEquality,[(Type,Type)])]
  -- ^ Given constraints
  -> [(Either NatEquality NatInEquality,[(Type,Type)])]
  -- ^ Wanted constraints
  -> TcPluginM SimplifyResult
simplifyNats (Opts {..}) eqsG eqsW =
    let eqs = map (second (const [])) eqsG ++ eqsW
    in  tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] [] eqs
  where
    -- If we allow negated numbers we simply do not emit the inequalities
    -- derived from the subtractions that are converted to additions with a
    -- negated operand
    subToPred | negNumbers = const []
              | otherwise  = map subtractionToPred

    simples :: [CoreUnify]
            -> [((EvTerm, Ct), [Ct])]
            -> [(CoreSOP,CoreSOP,Bool)]
            -> [(Either NatEquality NatInEquality,[(Type,Type)])]
            -> [(Either NatEquality NatInEquality,[(Type,Type)])]
            -> TcPluginM SimplifyResult
    simples _subst evs _leqsG _xs [] = return (Simplified evs)
    simples subst evs leqsG xs (eq@(Left (ct,u,v),k):eqs') = do
      let u' = substsSOP subst u
          v' = substsSOP subst v
      ur <- unifyNats ct u' v'
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win -> do
          evs' <- maybe evs (:evs) <$> evMagic ct empty (subToPred k)
          simples subst evs' leqsG [] (xs ++ eqs')
        Lose -> if null evs && null eqs'
                   then return (Impossible (fst eq))
                   else simples subst evs leqsG xs eqs'
        Draw [] -> simples subst evs [] (eq:xs) eqs'
        Draw subst' -> do
          evM <- evMagic ct empty (map unifyItemToPredType subst' ++
                                   subToPred k)
          let leqsG' | isGiven (ctEvidence ct) = eqToLeq u' v' ++ leqsG
                     | otherwise  = leqsG
          case evM of
            Nothing -> simples subst evs leqsG' xs eqs'
            Just ev ->
              simples (substsSubst subst' subst ++ subst')
                      (ev:evs) leqsG' [] (xs ++ eqs')
    simples subst evs leqsG xs (eq@(Right (ct,u@(x,y,b)),k):eqs') = do
      let u'    = substsSOP subst (subtractIneq u)
          x'    = substsSOP subst x
          y'    = substsSOP subst y
          uS    = (x',y',b)
          leqsG' | isGiven (ctEvidence ct) = (x',y',b):leqsG
                 | otherwise               = leqsG
          ineqs = concat [ leqsG
                         , map (substLeq subst) leqsG
                         , map snd (rights (map fst eqsG))
                         ]
      tcPluginTrace "unifyNats(ineq) results" (ppr (ct,u,u',ineqs))
      case runWriterT (isNatural u') of
        Just (True,knW)  -> do
          evs' <- maybe evs (:evs) <$> evMagic ct knW (subToPred k)
          simples subst evs' leqsG' xs eqs'

        Just (False,_) -> return (Impossible (fst eq))
        Nothing
          -- This inequality is either a given constraint, or it is a wanted
          -- constraint, which in normal form is equal to another given
          -- constraint, hence it can be solved.
          | or (mapMaybe (solveIneq depth u) ineqs) ||
          -- Or the above, but with valid substitutions applied to the wanted.
            or (mapMaybe (solveIneq depth uS) ineqs) ||
          -- Or it is an inequality that can be instantly solved, such as
          -- `1 <= x^y`
            instantSolveIneq depth u
          -> do
            evs' <- maybe evs (:evs) <$> evMagic ct empty (subToPred k)
            simples subst evs' leqsG' xs eqs'
          | otherwise
          -> simples subst evs leqsG (eq:xs) eqs'

    eqToLeq x y = [(x,y,True),(y,x,True)]
    substLeq s (x,y,b) = (substsSOP s x, substsSOP s y, b)

-- Extract the Nat equality constraints
toNatEquality :: Ct -> Maybe (Either NatEquality NatInEquality,[(Type,Type)])
toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      -> go t1 t2
    _ -> Nothing
  where
    go (TyConApp tc xs) (TyConApp tc' ys)
      | tc == tc'
      , null ([tc,tc'] `intersect` [typeNatAddTyCon,typeNatSubTyCon
                                   ,typeNatMulTyCon,typeNatExpTyCon])
      = case filter (not . uncurry eqType) (zip xs ys) of
          [(x,y)]
            | isNatKind (typeKind x)
            , isNatKind (typeKind y)
            , let (x',k1) = runWriter (normaliseNat x)
            , let (y',k2) = runWriter (normaliseNat y)
            -> Just (Left (ct, x', y'),k1 ++ k2)
          _ -> Nothing
      | tc == typeNatLeqTyCon
      , [x,y] <- xs
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      , let ks      = k1 ++ k2
      = case tc' of
         _ | tc' == promotedTrueDataCon
           -> Just (Right (ct, (x', y', True)), ks)
         _ | tc' == promotedFalseDataCon
           -> Just (Right (ct, (x', y', False)), ks)
         _ -> Nothing

    go x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      = Just (Left (ct,x',y'),k1 ++ k2)
      | otherwise
      = Nothing

    isNatKind :: Kind -> Bool
    isNatKind = (`eqType` typeNatKind)

unifyItemToPredType :: CoreUnify -> (PredType,Kind)
unifyItemToPredType ui =
    (mkPrimEqPred ty1 ty2,typeNatKind)
  where
    ty1 = case ui of
            SubstItem {..} -> mkTyVarTy siVar
            UnifyItem {..} -> reifySOP siLHS
    ty2 = case ui of
            SubstItem {..} -> reifySOP siSOP
            UnifyItem {..} -> reifySOP siRHS

evMagic :: Ct -> Set CType -> [(PredType,Kind)] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic ct knW preds = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> do
    let predTypes = map fst preds
        predKinds = map snd preds
#if MIN_VERSION_ghc(8,4,1)
    holes <- mapM (newCoercionHole . uncurry mkPrimEqPred . getEqPredTys) predTypes
#else
    holes <- replicateM (length preds) newCoercionHole
#endif
    knWanted <- mapM (mkKnWanted ct) (toList knW)
    let newWanted = knWanted ++ zipWith (unifyItemToCt (ctLoc ct)) predTypes holes
        ctEv      = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
#if MIN_VERSION_ghc(8,4,1)
        holeEvs   = map mkHoleCo holes
#else
        holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes predTypes
#endif
    forallEv <- mkForAllCos <$> (mapM mkCoVar predKinds) <*> pure ctEv
    let finalEv = foldl mkInstCo forallEv holeEvs
#if MIN_VERSION_ghc(8,5,0)
    return (Just ((EvExpr (Coercion finalEv), ct),newWanted))
#else
    return (Just ((EvCoercion finalEv, ct),newWanted))
#endif
  _ -> return Nothing
  where
    mkCoVar k = (,natReflCo) <$> (newFlexiTyVar k)
      where
        natReflCo = mkNomReflCo k

mkKnWanted
  :: Ct
  -> CType
  -> TcPluginM Ct
mkKnWanted ct (CType ty) = do
  kc_clas <- tcLookupClass knownNatClassName
  let kn_pred = mkClassPred kc_clas [ty]
  wantedCtEv <- TcPluginM.newWanted (ctLoc ct) kn_pred
  let wanted = mkNonCanonical wantedCtEv
      -- Set the source-location of the new wanted constraint to the source
      -- location of the [W]anted constraint we are currently trying to solve
      ct_ls   = ctLocSpan (ctLoc ct)
      ctl     = ctEvLoc  wantedCtEv
      wanted' = setCtLoc wanted (setCtLocSpan ctl ct_ls)
  return wanted'

unifyItemToCt :: CtLoc
              -> PredType
              -> CoercionHole
              -> Ct
unifyItemToCt loc pred_type hole =
  mkNonCanonical
    (CtWanted
      pred_type
      (HoleDest hole)
#if MIN_VERSION_ghc(8,2,0)
      WDeriv
#endif
      loc)
