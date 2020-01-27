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
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE ViewPatterns    #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Control.Arrow       (second)
import Control.Monad       ((<=<), forM)
#if !MIN_VERSION_ghc(8,4,1)
import Control.Monad       (replicateM)
#endif
import Control.Monad.Trans.Writer.Strict
import Data.Either         (lefts, rights)
import Data.List           (intersect, stripPrefix, find)
import Data.List.Extra     (nubOrd)
import Data.Maybe          (mapMaybe, catMaybes)
import Data.Set            (Set, empty, toList, notMember, fromList, union, insert)
import GHC.TcPluginM.Extra (tracePlugin, newGiven, newWanted)
import qualified GHC.TcPluginM.Extra as TcPluginM
#if MIN_VERSION_ghc(8,4,0)
import GHC.TcPluginM.Extra (flattenGivens, substCt)
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
#if MIN_VERSION_ghc(8,6,0)
import TcEvidence (evCast)
#endif
#if !MIN_VERSION_ghc(8,4,0)
import TcPluginM  (zonkCt)
#endif
import TcPluginM  (TcPluginM, tcPluginTrace, tcPluginIO)
import Type       (Kind, PredType, eqType, mkTyVarTy)
import TysWiredIn (typeNatKind)

import Coercion   (CoercionHole, Role (..), mkForAllCos, mkHoleCo, mkInstCo,
                   mkNomReflCo, mkUnivCo)
import TcPluginM  (newCoercionHole, newFlexiTyVar, tcLookupClass)
import TcRnTypes  (TcPlugin (..), TcPluginResult(..))
import TyCoRep    (UnivCoProvenance (..))
import TcType     (isEqPred)
import TyCoRep    (Type (..))
import TcTypeNats (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
                   typeNatSubTyCon)

import TcTypeNats (typeNatLeqTyCon)
import TysWiredIn (promotedFalseDataCon, promotedTrueDataCon)
import UniqSet    (elementOfUniqSet)
import Data.IORef

#if MIN_VERSION_ghc(8,10,0)
import Constraint
  (Ct (..), CtEvidence (..), CtLoc, TcEvDest (..), ctEvidence, ctEvLoc, ctEvPred,
   ctLoc, ctLocSpan, isGiven, isWanted, mkNonCanonical, setCtLoc, setCtLocSpan)
import Predicate
  (EqRel (NomEq), Pred (EqPred), classifyPredType, getEqPredTys, mkClassPred,
   mkPrimEqPred)
import Type (typeKind)
#else
import TcRnTypes
  (Ct (..), CtEvidence (..), CtLoc, TcEvDest (..), ctEvidence, ctEvLoc, ctEvPred,
   ctLoc, ctLocSpan, isGiven, isWanted, mkNonCanonical, setCtLoc, setCtLocSpan)
import TcType (typeKind)
import Type
  (EqRel (NomEq), PredTree (EqPred), classifyPredType, getEqPredTys, mkClassPred,
   mkPrimEqPred)
#endif

#if MIN_VERSION_ghc(8,10,0)
import Constraint (ctEvExpr)
#elif MIN_VERSION_ghc(8,6,0)
import TcRnTypes  (ctEvExpr)
#else
import TcRnTypes  (ctEvTerm)
#endif

#if MIN_VERSION_ghc(8,2,0)
#if MIN_VERSION_ghc(8,10,0)
import Constraint (ShadowInfo (WDeriv))
#else
import TcRnTypes  (ShadowInfo (WDeriv))
#endif
#endif

#if MIN_VERSION_ghc(8,10,0)
import TcType (isEqPrimPred)
#endif

-- internal
import GHC.TypeLits.Normalise.SOP
import GHC.TypeLits.Normalise.Unify

#if !MIN_VERSION_ghc(8,10,0)
isEqPrimPred :: PredType -> Bool
isEqPrimPred = isEqPred
#endif

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
  TcPlugin { tcPluginInit  = tcPluginIO $ newIORef empty
           , tcPluginSolve = decideEqualSOP opts
           , tcPluginStop  = const (return ())
           }
newtype OrigCt = OrigCt { runOrigCt :: Ct }

decideEqualSOP
  :: Opts
  -> IORef (Set CType)
      -- ^ Givens that is already generated.
      --   We have to generate new givens at most once;
      --   otherwise GHC will loop indefinitely.
  -> [Ct]
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginResult

-- Simplification phase: Derives /simplified/ givens;
-- we can reduce given constraints like @Show (Foo (n + 2))@
-- to its normal form @Show (Foo (2 + n))@, which is eventually
-- useful in solving phase.
--
-- This helps us to solve /indirect/ constraints;
-- without this phase, we cannot derive, e.g.,
-- @IsVector UVector (Fin (n + 1))@ from
-- @Unbox (1 + n)@!
decideEqualSOP opts gen'd givens _deriveds [] = do
    done <- tcPluginIO $ readIORef gen'd
#if MIN_VERSION_ghc(8,4,0)
    let simplGivens = flattenGivens givens
#else
    simplGivens <- mapM zonkCt givens
#endif
    let reds =
          filter (\(_,(_,_,v)) -> null v || negNumbers opts) $
          reduceGivens opts done simplGivens
        newlyDone = map (\(_,(prd, _,_)) -> CType prd) reds
    tcPluginIO $
      modifyIORef' gen'd $ union (fromList newlyDone)
    newGivens <- forM reds $ \(origCt, (pred', evTerm, _)) ->
      mkNonCanonical' (ctLoc origCt) <$> newGiven (ctLoc origCt) pred' evTerm
    return (TcPluginOk [] newGivens)

-- Solving phase.
-- Solves in/equalities on Nats and simplifiable constraints
-- containing naturals.
decideEqualSOP opts gen'd givens  _deriveds wanteds = do
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
#if MIN_VERSION_ghc(8,4,0)
    let simplGivens = givens ++ flattenGivens givens
        subst = fst $ unzip $ TcPluginM.mkSubst' givens
        wanteds0 = map (\ct -> (OrigCt ct,substCt subst ct)) wanteds
#else
    let wanteds0 = map (\ct -> (OrigCt ct, ct)) wanteds
    simplGivens <- mapM zonkCt givens
#endif
    let wanteds' = filter (isWanted . ctEvidence) wanteds
        unit_wanteds = mapMaybe toNatEquality wanteds'
        nonEqs = filter (not . (\p -> isEqPred p || isEqPrimPred p) . ctEvPred . ctEvidence.snd)
                 $ filter (isWanted. ctEvidence.snd) wanteds0
    done <- tcPluginIO $ readIORef gen'd
    let redGs = reduceGivens opts done simplGivens
        newlyDone = map (\(_,(prd, _,_)) -> CType prd) redGs
    redGivens <- forM redGs $ \(origCt, (pred', evTerm, _)) ->
      mkNonCanonical' (ctLoc origCt) <$> newGiven (ctLoc origCt) pred' evTerm
    reducible_wanteds
      <- catMaybes <$>
            mapM
              (\(origCt, ct) -> fmap (runOrigCt origCt,) <$>
                  reduceNatConstr (simplGivens ++ redGivens) ct
              )
            nonEqs
    if null unit_wanteds && null reducible_wanteds
    then return $ TcPluginOk [] []
    else do
        -- Since reducible wanteds also can have some negation/subtraction
        -- subterms, we have to make sure appropriate inequalities to hold.
        -- Here, we generate such additional inequalities for reduction
        -- that is to be added to new [W]anteds.
        ineqForRedWants <- fmap concat $ forM redGs $ \(ct, (_,_, ws)) -> forM ws $
          fmap (mkNonCanonical' (ctLoc ct)) . newWanted (ctLoc ct)
        tcPluginIO $
          modifyIORef' gen'd $ union (fromList newlyDone)
        let unit_givens = mapMaybe toNatEquality simplGivens
        sr <- solveWanted opts unit_givens unit_wanteds
        tcPluginTrace "normalised" (ppr sr)
        reds <- forM reducible_wanteds $ \(origCt,(term, ws)) -> do
          wants <- fmap fst $ evSubtPreds origCt $ subToPred opts ws
          return ((term, origCt), wants)
        case sr of
          Simplified evs -> do
            let simpld = filter (isWanted . ctEvidence . (\((_,x),_) -> x)) evs
                (solved',newWanteds) = second concat (unzip $ simpld ++ reds)
            return (TcPluginOk solved' $ newWanteds ++ ineqForRedWants)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality   = (Ct,CoreSOP,CoreSOP)
type NatInEquality = (Ct,(CoreSOP,CoreSOP,Bool))

reduceGivens :: Opts -> Set CType -> [Ct] -> [(Ct, (Type, EvTerm, [PredType]))]
reduceGivens opts done givens =
  let nonEqs =
        [ ct
        | ct <- givens
        , let ev = ctEvidence ct
              prd = ctEvPred ev
        , isGiven ev
        , not $ (\p -> isEqPred p || isEqPrimPred p) prd
        ]
  in filter
      (\(_, (prd, _, _)) ->
        notMember (CType prd) done
      )
    $ mapMaybe
      (\ct -> (ct,) <$> tryReduceGiven opts givens ct)
      nonEqs

tryReduceGiven
  :: Opts -> [Ct] -> Ct
  -> Maybe (PredType, EvTerm, [PredType])
tryReduceGiven opts simplGivens ct = do
    let (mans, ws) =
          runWriter $ normaliseNatEverywhere $
          ctEvPred $ ctEvidence ct
        ws' = [ p
              | (p, _) <- subToPred opts ws
              , all (not . (`eqType` p). ctEvPred . ctEvidence) simplGivens
              ]
    pred' <- mans
    return (pred', toReducedDict (ctEvidence ct) pred', ws')

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

reduceNatConstr :: [Ct] -> Ct -> TcPluginM (Maybe (EvTerm, [(Type, Type)]))
reduceNatConstr givens ct =  do
  let pred0 = ctEvPred $ ctEvidence ct
      (mans, tests) = runWriter $ normaliseNatEverywhere pred0
  case mans of
    Nothing -> return Nothing
    Just pred' -> do
      case find ((`eqType` pred') .ctEvPred . ctEvidence) givens of
        Nothing -> return Nothing
        Just c  -> return (Just (toReducedDict (ctEvidence c) pred0, tests))

toReducedDict :: CtEvidence -> PredType -> EvTerm
toReducedDict ct pred' =
  let pred0 = ctEvPred ct
      evCo = mkUnivCo (PluginProv "ghc-typelits-natnormalise")
              Representational
              pred0 pred'
#if MIN_VERSION_ghc(8,6,0)
      ev = ctEvExpr ct
             `evCast` evCo
#else
      ev = ctEvTerm ct `EvCast` evCo
#endif
  in ev

data SimplifyResult
  = Simplified [((EvTerm,Ct),[Ct])]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

findGivenSubst ::
  [(Either NatEquality NatInEquality, [(Type, Type)])] ->
  TcPluginM [CoreUnify]
findGivenSubst = go [] []
 where
  go ::
    [CoreUnify] ->
    [(Either NatEquality NatInEquality, [(Type, Type)])] ->
    [(Either NatEquality NatInEquality, [(Type, Type)])] ->
    TcPluginM [CoreUnify]
  go subst _        [] = pure subst
  go subst tryAgain (eq@(Left (ct,u,v),_k):eqs) = do
    let uvs = rewriteEQ False subst (u,v)
    urs <- mapM (uncurry (unifyNats ct)) uvs
    case foldr smashDraw Lose urs of
      Draw qs@(_:_) -> go (qs ++ subst) [] (tryAgain ++ eqs)
      _ -> go subst (eq:tryAgain) eqs
  go subst tryAgain (_:eqs) = go subst tryAgain eqs

  -- We want to collect as many potential new unifiers as possible.
  smashDraw (Draw s1) (Draw s2) = Draw (nubOrd (s1 ++ s2))
  smashDraw (Draw s) _ = Draw s
  smashDraw _ (Draw s) = Draw s
  smashDraw _ r        = r

-- | Witness that equality is a symmetric relation
newtype SymSOP = SymSOP (CoreSOP, CoreSOP)

instance Eq SymSOP where
  (SymSOP (p,q)) == (SymSOP (x,y)) =
    case p == x of
      False -> p == y && q == x
      True  -> q == y

instance Ord SymSOP where
  compare (SymSOP (p,q)) (SymSOP (x,y)) =
    case compare p x of
      LT -> case compare p y of
        EQ -> case compare q x of
          EQ -> EQ
          _  -> LT
        _ -> LT
      EQ -> compare q y
      GT -> GT

rewriteEQ ::
  Bool ->
  [CoreUnify] ->
  (CoreSOP, CoreSOP) ->
  [(CoreSOP, CoreSOP)]
rewriteEQ isW subst = go empty
 where
  go hist (u,v) =
    let
      hist1    = insert (SymSOP (u,v)) hist
      rewrites = mapMaybe (rewrite (u,v)) subst
      new      = nubOrd (filter ((`notMember` hist1) . SymSOP) rewrites)
    in (u,v):concatMap (go hist1) new

  rewrite _     UnifyItem {}    = Nothing
  rewrite (p,q) (SubstItem x e) =
    let p1 = substSOP x e p
        q1 = substSOP x e q
    in  if isW || p1 /= q1 then
          Just (substSOP x e p, substSOP x e q)
        else
          Nothing

rewriteINEQ ::
  [CoreUnify] ->
  (CoreSOP,CoreSOP,Bool) ->
  [(CoreSOP,CoreSOP,Bool)]
rewriteINEQ subst = go empty
 where
  go hist (u,v,b) =
    let hist1    = insert (u,v,b) hist
        rewrites = mapMaybe (rewrite (u,v,b)) subst
        new      = nubOrd (filter (`notMember` hist1) rewrites)
    in  (u,v,b):concatMap (go hist1) new

  rewrite _       UnifyItem {}    = Nothing
  rewrite (p,q,z) (SubstItem x e) =
    let p1 = substSOP x e p
        q1 = substSOP x e q
    in  if p1 /= q1 then
          Just (substSOP x e p, substSOP x e q, z)
        else
          Nothing

solveWanted ::
  -- | Solver options (depth, whether to allow integers, etc.)
  Opts ->
  -- | Given constraints
  [(Either NatEquality NatInEquality,[(Type,Type)])] ->
  -- | Wanted constraints
  [(Either NatEquality NatInEquality,[(Type,Type)])] ->
  TcPluginM SimplifyResult
solveWanted opts@Opts {..} eqsG eqsW = do
  subst <- nubOrd . concatMap mkSubst <$> findGivenSubst eqsG
  tcPluginTrace "solveWanted eqsG:" (ppr eqsG)
  tcPluginTrace "solveWanted subst:" (ppr (subst))
  go subst [] eqsW
 where
  go _     evs [] = pure (Simplified evs)
  go subst evs ((Left (ct,u,v),kW):eqs) = do
    (subst1,s) <- goSingleWantedEq subst (ct,u,v,kW)
    case s of
      Simplified ev -> go subst1 (ev ++ evs) eqs
      i -> if null evs && null eqs then
             pure i
           else
             go subst1 evs eqs
  go subst evs ((Right (ct,(u,v,b)),kW):eqs) = do
    s <- goSingleWantedInEq subst (ct,u,v,b,kW)
    case s of
      Simplified ev -> go subst (ev ++ evs) eqs
      i -> if null evs && null eqs then
             pure i
           else
             go subst evs eqs

  goSingleWantedEq
    :: [CoreUnify]
    -> (Ct,CoreSOP,CoreSOP,[(Type,Type)])
    -> TcPluginM ([CoreUnify],SimplifyResult)
  goSingleWantedEq subst (ct,u,v,kW) = do
    tcPluginTrace "goSingleWanted" (ppr (ct,u,v,subst))
    let uvs = rewriteEQ True subst (u,v)
    urs <- mapM (uncurry (unifyNats ct)) uvs
    case foldr (smashResult (u,v)) (Draw []) urs of
      Win     -> maybe (subst,Simplified []) ((subst,) . Simplified . (:[])) <$>
                       evMagic ct empty (subToPred opts kW)
      Lose    -> pure (subst,Impossible (Left (ct,u,v)))
      Draw [] -> pure (subst,Simplified [])
      Draw s  ->
        let subst1 = nubOrd (concatMap mkSubst s ++ subst)
        in  maybe (subst,Simplified []) ((subst1,) . Simplified . (:[])) <$>
                  evMagic ct empty (map unifyItemToPredType s ++ subToPred opts kW)

  mkSubst UnifyItem {} = []
  mkSubst (SubstItem x e)
    | S [P [V y]] <- e
    = if x /= y then [SubstItem x e, SubstItem y (S [P [(V x)]])] else []
    | otherwise
    = [SubstItem x e]

  smashResult _ Lose       _          = Lose
  smashResult _ _          Lose       = Lose
  smashResult _ Win        _          = Win
  smashResult _ _          Win        = Win
  -- We want to pick the unification result that has the least, though non-zero,
  -- number of unifiers to show equality of the LHS and RHS of the wanted
  -- constraint.
  smashResult uvW (Draw s1)  (Draw s2)  =
    let s1F = filter (simpleSubst uvW) s1
        s2F = filter (simpleSubst uvW) s2
    in  case s1F of
          [] -> Draw s2F
          _  -> case s2F of
            [] -> Draw s1F
            _  -> if length s1F <= length s2F
                     then Draw s1F
                     else Draw s2F

  -- Assert good unifications
  simpleSubst _ UnifyItem {}    = True
  simpleSubst (lhs,rhs) (SubstItem v s)
    | S [P [V _]] <- s
    = True
    | otherwise
    = not
      -- No [v := v + 1]
      ( v `elementOfUniqSet` fvSOP s ||
      -- No [v := LHS] or [v := RHS] where the substitution is equal to the
      -- original LSH or RHS of the wanted constraint '[W] LSH ~ RHS'
        s == lhs || s == rhs
      )

  goSingleWantedInEq
    :: [CoreUnify]
    -> (Ct,CoreSOP,CoreSOP,Bool,[(Type,Type)])
    -> TcPluginM SimplifyResult
  goSingleWantedInEq subst (ct,u,v,b,kW) = do
    let ineqs  = map snd (rights (map fst eqsG))
        eqs    = map (\(_,x,y) -> (x,y)) (lefts (map fst eqsG))
        ineqs1 = nubOrd (concatMap (rewriteINEQ subst) ineqs)
        ineqs2 = nubOrd (concatMap (concatMap eqToLeq . rewriteEQ False subst) eqs)
        ineqs3 = ineqs1 ++ ineqs2
        uvbs   = rewriteINEQ subst (u,v,b)
        zs     = map subtractIneq uvbs
        solved = mapMaybe runWriterT
                   (-- When `LHS <= RHS ~ True` and `RHS-LHS` is a natural number, or
                    -- When `LHS <= RHS ~ False` and `LHS-RHS` is a natural number,
                    -- Then the equation is true.
                    map isNatural zs ++
                    -- This inequality is either a given constraint, or it is a
                    -- wanted constraint, which in normal form is equal to
                    -- another given constraint, hence it can be solved.
                    concatMap (\uvb -> map (solveIneq depth uvb) ineqs3) uvbs ++
                    -- Or it is an inequality that can be instantly solved, such
                    -- as `1 <= x^y`
                    map (instantSolveIneq depth) uvbs)
        smallest = solvedInEqSmallestConstraint solved
    tcPluginTrace "goSingleWantedInEq" (ppr (ct,uvbs,ineqs3))
    case smallest of
      (True,knW) -> maybe (Simplified []) (Simplified . (:[])) <$>
                          evMagic ct knW (subToPred opts kW)
      _ -> pure (Simplified [])

  eqToLeq (x,y) = [(x,y,True),(y,x,True)]

-- If we allow negated numbers we simply do not emit the inequalities
-- derived from the subtractions that are converted to additions with a
-- negated operand
subToPred :: Opts -> [(Type, Type)] -> [(PredType, Kind)]
subToPred Opts{..}
  | negNumbers = const []
  | otherwise  = map subtractionToPred

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

evSubtPreds :: Ct -> [(PredType,Kind)] -> TcPluginM ([Ct], [CoercionHole])
evSubtPreds ct preds = do
  let predTypes = map fst preds
#if MIN_VERSION_ghc(8,4,1)
  holes <- mapM (newCoercionHole . uncurry mkPrimEqPred . getEqPredTys) predTypes
#else
  holes <- replicateM (length preds) newCoercionHole
#endif
  return (zipWith (unifyItemToCt (ctLoc ct)) predTypes holes, holes)

evMagic :: Ct -> Set CType -> [(PredType,Kind)] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic ct knW preds = case classifyPredType $ ctEvPred $ ctEvidence ct of
  EqPred NomEq t1 t2 -> do
    (holeWanteds, holes) <- evSubtPreds ct preds
    let predKinds = map snd preds
    knWanted <- mapM (mkKnWanted ct) (toList knW)
    let newWant = knWanted ++ holeWanteds
        ctEv      = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
#if MIN_VERSION_ghc(8,4,1)
        holeEvs   = map mkHoleCo holes
#else
        predTypes = map fst preds
        holeEvs   = zipWith (\h p -> uncurry (mkHoleCo h Nominal) (getEqPredTys p)) holes predTypes
#endif
    forallEv <- mkForAllCos <$> mapM mkCoVar predKinds <*> pure ctEv
    let finalEv = foldl mkInstCo forallEv holeEvs
#if MIN_VERSION_ghc(8,5,0)
    return (Just ((EvExpr (Coercion finalEv), ct),newWant))
#else
    return (Just ((EvCoercion finalEv, ct),newWant))
#endif
  _ -> return Nothing
  where
    mkCoVar k = (,natReflCo) <$> newFlexiTyVar k
      where
        natReflCo = mkNomReflCo k

mkNonCanonical' :: CtLoc -> CtEvidence -> Ct
mkNonCanonical' origCtl ev =
  let ct_ls   = ctLocSpan origCtl
      ctl     = ctEvLoc  ev
  in setCtLoc (mkNonCanonical ev) (setCtLocSpan ctl ct_ls)

mkKnWanted
  :: Ct
  -> CType
  -> TcPluginM Ct
mkKnWanted ct (CType ty) = do
  kc_clas <- tcLookupClass knownNatClassName
  let kn_pred = mkClassPred kc_clas [ty]
  wantedCtEv <- TcPluginM.newWanted (ctLoc ct) kn_pred
  let wanted' = mkNonCanonical' (ctLoc ct) wantedCtEv
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
