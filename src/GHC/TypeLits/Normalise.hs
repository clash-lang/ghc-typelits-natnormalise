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

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ExplicitNamespaces    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.Normalise
  ( plugin )
where

-- base
import Control.Arrow
  ( second )
import Control.Monad
  ( (<=<), forM )
import Control.Monad.IO.Class
  ( liftIO )
import Control.Monad.Trans.Writer.Strict
  ( WriterT(runWriterT), runWriter )
import Data.Either
  ( partitionEithers, rights )
import Data.IORef
  ( IORef, newIORef, readIORef, modifyIORef' )
import Data.List
  ( partition, stripPrefix, find )
import qualified Data.List.NonEmpty as NE
import Data.Maybe
  ( mapMaybe, catMaybes )
import Data.Set
  ( Set, empty, toList, notMember, fromList, union )
import Text.Read
  ( readMaybe )

-- ghc
import GHC.Builtin.Names
  ( knownNatClassName )
import GHC.Builtin.Types.Literals
  ( typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon, typeNatSubTyCon )

-- ghc-tcplugin-api
import GHC.TcPlugin.API
import GHC.TcPlugin.API.TyConSubst
  ( TyConSubst, mkTyConSubst, splitTyConApp_upTo )
import GHC.Plugins
  ( Plugin(..), defaultPlugin, purePlugin )
import GHC.Utils.Outputable
  ( ($$), (<+>), text )

-- ghc-typelits-natnormalise
import GHC.TypeLits.Normalise.Compat
import GHC.TypeLits.Normalise.SOP
  ( SOP(S), Product(P), Symbol(V) )
import GHC.TypeLits.Normalise.Unify

--------------------------------------------------------------------------------

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
  { tcPlugin = \ p -> do opts <- foldr id defaultOpts <$> traverse parseArgument p
                         return $ mkTcPlugin $ normalisePlugin opts
  , pluginRecompile = purePlugin
  }
 where
  parseArgument "allow-negated-numbers" = Just (\ opts -> opts { negNumbers = True })
  parseArgument (readMaybe <=< stripPrefix "depth=" -> Just depth) = Just (\ opts -> opts { depth })
  parseArgument _ = Nothing
  defaultOpts = Opts { negNumbers = False, depth = 5 }

data Opts = Opts { negNumbers :: Bool, depth :: Word }

normalisePlugin :: Opts -> TcPlugin
normalisePlugin opts =
  TcPlugin { tcPluginInit    = lookupExtraDefs
           , tcPluginSolve   = decideEqualSOP opts
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop    = const (return ())
           }

data ExtraDefs
  = ExtraDefs
    { gen'dRef :: IORef (Set CType)
    , tyCons :: LookedUpTyCons
    }

lookupExtraDefs :: TcPluginM Init ExtraDefs
lookupExtraDefs = do
  ref <- liftIO (newIORef empty)
  tcs <- lookupTyCons
  return $
    ExtraDefs
      { gen'dRef = ref
      , tyCons = tcs
      }

decideEqualSOP
  :: Opts
  -> ExtraDefs
      -- ^ 1. Givens that is already generated.
      --   We have to generate new givens at most once;
      --   otherwise GHC will loop indefinitely.
      --
      --
      --   2. For GHc 9.2: TyCon of Data.Type.Ord.OrdCond
      --      For older: TyCon of GHC.TypeLits.<=?
  -> [Ct]
  -> [Ct]
  -> TcPluginM Solve TcPluginSolveResult

-- Simplification phase: Derives /simplified/ givens;
-- we can reduce given constraints like @Show (Foo (n + 2))@
-- to its normal form @Show (Foo (2 + n))@, which is eventually
-- useful in solving phase.
--
-- This helps us to solve /indirect/ constraints;
-- without this phase, we cannot derive, e.g.,
-- @IsVector UVector (Fin (n + 1))@ from
-- @Unbox (1 + n)@!
decideEqualSOP opts (ExtraDefs { gen'dRef = gen'd, tyCons = tcs }) givens [] = do
    done <- liftIO $ readIORef gen'd
    let reds =
          filter (\(_,(_,_,v)) -> null v || negNumbers opts) $
          reduceGivens opts tcs done givens
        newlyDone = map (\(_,(prd, _,_)) -> CType prd) reds
    liftIO $
      modifyIORef' gen'd $ union (fromList newlyDone)
    newGivens <- forM reds $ \(origCt, (pred', evTerm, _)) ->
      mkNonCanonical <$> newGiven (ctLoc origCt) pred' evTerm
    return (TcPluginOk [] newGivens)

-- Solving phase.
-- Solves in/equalities on Nats and simplifiable constraints
-- containing naturals.
decideEqualSOP opts (ExtraDefs { gen'dRef = gen'd, tyCons = tcs }) givens wanteds0 = do
    deriveds <- askDeriveds
    let wanteds = if null wanteds0
                  then []
                  else wanteds0 ++ deriveds
        givensTyConSubst = mkTyConSubst givens
        unit_wanteds = concatMap (toNatEquality tcs givensTyConSubst) wanteds
        nonEqs = filter ( not
                        . (\p -> isEqPred p || isEqClassPred p)
                        . ctEvPred
                        . ctEvidence )
                 wanteds
    done <- liftIO $ readIORef gen'd
    let redGs = reduceGivens opts tcs done givens
        newlyDone = map (\(_,(prd, _,_)) -> CType prd) redGs
    redGivens <- forM redGs $ \(origCt, (pred', evExpr, _)) ->
      mkNonCanonical <$> newGiven (ctLoc origCt) pred' evExpr
    reducible_wanteds
      <- catMaybes <$> mapM (\ct -> fmap (ct,) <$>
                                    reduceNatConstr (givens ++ redGivens) ct)
                            nonEqs
    if null unit_wanteds && null reducible_wanteds
    then return $ TcPluginOk [] []
    else do
        -- Since reducible wanteds also can have some negation/subtraction
        -- subterms, we have to make sure appropriate inequalities to hold.
        -- Here, we generate such additional inequalities for reduction
        -- that is to be added to new [W]anteds.
        ineqForRedWants <- fmap concat $ forM redGs $ \(ct, (_,_, ws)) -> forM ws $
          fmap mkNonCanonical . newWanted (ctLoc ct)
        liftIO $
          modifyIORef' gen'd $ union (fromList newlyDone)
        let unit_givens = concatMap (toNatEquality tcs givensTyConSubst) givens
        sr <- simplifyNats opts tcs unit_givens unit_wanteds
        tcPluginTrace "normalised" (ppr sr)
        reds <- forM reducible_wanteds $ \(origCt,(term, ws, wDicts)) -> do
          wants <- evSubtPreds (ctLoc origCt) $ subToPred opts tcs ws
          return ((term, origCt), wDicts ++ wants)
        case sr of
          Simplified evs -> do
            let simpld = filter (not . isGiven . ctEvidence . (\((_,x),_) -> x)) evs
                -- Only solve derived when we solved a wanted
                simpld1 = case filter (isWanted . ctEvidence . (\((_,x),_) -> x)) evs ++ reds of
                            [] -> []
                            _  -> simpld
                (solved',newWanteds) = second concat (unzip $ simpld1 ++ reds)
            return (TcPluginOk solved' $ newWanteds ++ ineqForRedWants)
          Impossible eq -> return (TcPluginContradiction [fromNatEquality eq])

type NatEquality   = (Ct,CoreSOP,CoreSOP)
type NatInEquality = (Ct,(CoreSOP,CoreSOP,Bool))

reduceGivens :: Opts -> LookedUpTyCons -> Set CType
             -> [Ct] -> [(Ct, (Type, EvTerm, [PredType]))]
reduceGivens opts tcs done givens =
  let nonEqs =
        [ ct
        | ct <- givens
        , let ev = ctEvidence ct
              prd = ctEvPred ev
        , isGiven ev
        , not $ (\p -> isEqPred p || isEqClassPred p ) prd
        ]
  in filter
      (\(_, (prd, _, _)) ->
        notMember (CType prd) done
      )
    $ mapMaybe
      (\ct -> (ct,) <$> tryReduceGiven opts tcs givens ct)
      nonEqs

tryReduceGiven
  :: Opts -> LookedUpTyCons
  -> [Ct] -> Ct
  -> Maybe (PredType, EvTerm, [PredType])
tryReduceGiven opts tcs simplGivens ct = do
    let (mans, ws) =
          runWriter $ normaliseNatEverywhere $
          ctEvPred $ ctEvidence ct
        ws' = [ p
              | p <- subToPred opts tcs ws
              , all (not . (`eqType` p). ctEvPred . ctEvidence) simplGivens
              ]
        -- deps = unitDVarSet (ctEvId ct)
    pred' <- mans
    return (pred', toReducedDict (ctEvidence ct) pred', ws')

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

reduceNatConstr :: [Ct] -> Ct -> TcPluginM Solve (Maybe (EvTerm, [(Type, Type)], [Ct]))
reduceNatConstr givens ct =  do
  let pred0 = ctEvPred $ ctEvidence ct
      (mans, tests) = runWriter $ normaliseNatEverywhere pred0
  case mans of
    Nothing -> return Nothing
    Just pred' -> do
      case find ((`eqType` pred') . ctEvPred . ctEvidence) givens of
        -- No existing evidence found
        Nothing
          | ClassPred cls _ <- classifyPredType pred'
          , className cls /= knownNatClassName
          -> do
              -- Create new evidence binding for normalized class constraint
              wtdDictCt <- mkNonCanonical <$> newWanted (ctLoc ct) pred'
              -- Evidence for current wanted is simply the coerced binding for
              -- the new binding
              let evCo = mkPluginUnivCo "ghc-typelits-natnormalise"
                           Representational
                           []
                           pred' pred0
                  ev = evCast (evId $ ctEvId wtdDictCt) evCo
              -- Use newly created coerced wanted as evidence, and emit the
              -- normalized wanted as a new constraint to solve.
              return (Just (EvExpr ev, tests, [wtdDictCt]))
          | otherwise
          -> return Nothing
        -- Use existing evidence
        Just c  -> return (Just (toReducedDict (ctEvidence c) pred0, tests, []))

toReducedDict :: CtEvidence -> PredType -> EvTerm
toReducedDict ct pred' =
  let pred0 = ctEvPred ct
      evCo = mkPluginUnivCo "ghc-typelits-natnormalise"
              Representational
              []
              pred0 pred'
      ev = evCast (ctEvExpr ct) evCo
  in EvExpr ev

data SimplifyResult
  = Simplified [((EvTerm,Ct),[Ct])]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats
  :: Opts
  -- ^ Allow negated numbers (potentially unsound!)
  -> LookedUpTyCons
  -> [(Either NatEquality NatInEquality,[(Type,Type)])]
  -- ^ Given constraints
  -> [(Either NatEquality NatInEquality,[(Type,Type)])]
  -- ^ Wanted constraints
  -> TcPluginM Solve SimplifyResult
simplifyNats opts@Opts {..} tcs eqsG eqsW = do
    let eqsG1 = map (second (const ([] :: [(Type,Type)]))) eqsG
        (varEqs,otherEqs) = partition isVarEqs eqsG1
        fancyGivens = concatMap (makeGivensSet otherEqs) varEqs
    case varEqs of
      [] -> do
        let eqs = otherEqs ++ eqsW
        tcPluginTrace "simplifyNats" (ppr eqs)
        simples [] [] [] [] [] eqs
      _  -> do
        tcPluginTrace ("simplifyNats(backtrack: " ++ show (length fancyGivens) ++ ")")
                      (ppr varEqs)

        allSimplified <- forM fancyGivens $ \v -> do
          let eqs = v ++ eqsW
          tcPluginTrace "simplifyNats" (ppr eqs)
          simples [] [] [] [] [] eqs

        pure (foldr findFirstSimpliedWanted (Simplified []) allSimplified)
  where
    simples :: [Coercion]
            -> [CoreUnify]
            -> [((EvTerm, Ct), [Ct])]
            -> [(CoreSOP,CoreSOP,Bool)]
            -> [(Either NatEquality NatInEquality,[(Type,Type)])]
            -> [(Either NatEquality NatInEquality,[(Type,Type)])]
            -> TcPluginM Solve SimplifyResult
    simples _ _subst evs _leqsG _xs [] = return (Simplified evs)
    simples deps subst evs leqsG xs (eq@(Left (ct,u,v),k):eqs') = do
      let u' = substsSOP subst u
          v' = substsSOP subst v
      ur <- unifyNats ct u' v'
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win -> do
          evs' <- maybe evs (:evs) <$> evMagic tcs ct deps empty (subToPred opts tcs k)
          simples deps subst evs' leqsG [] (xs ++ eqs')
        Lose -> if null evs && null eqs'
                   then return (Impossible (fst eq))
                   else simples deps subst evs leqsG xs eqs'
        Draw [] -> simples deps subst evs [] (eq:xs) eqs'
        Draw subst' -> do
          evM <- evMagic tcs ct deps empty (map unifyItemToPredType subst' ++
                                            subToPred opts tcs k)
          let (leqsG1, deps1)
                | isGiven (ctEvidence ct) = ( eqToLeq u' v' ++ leqsG
                                            , ctEvCoercion (ctEvidence ct):deps)
                | otherwise               = (leqsG, deps)
          case evM of
            Nothing -> simples deps1 subst evs leqsG1 xs eqs'
            Just ev ->
              simples (ctEvCoercion (ctEvidence ct):deps)
                      (substsSubst subst' subst ++ subst')
                      (ev:evs) leqsG1 [] (xs ++ eqs')
    simples deps subst evs leqsG xs (eq@(Right (ct,u@(x,y,b)),k):eqs') = do
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
          evs' <- maybe evs (:evs) <$> evMagic tcs ct deps knW (subToPred opts tcs k)
          simples deps subst evs' leqsG' xs eqs'

        Just (False,_) | null k -> return (Impossible (fst eq))
        _ -> do
          let solvedIneq = mapMaybe runWriterT
                 -- it is an inequality that can be instantly solved, such as
                 -- `1 <= x^y`
                 -- OR
                (instantSolveIneq depth u:
                instantSolveIneq depth uS:
                -- This inequality is either a given constraint, or it is a wanted
                -- constraint, which in normal form is equal to another given
                -- constraint, hence it can be solved.
                -- OR
                map (solveIneq depth u) ineqs ++
                -- The above, but with valid substitutions applied to the wanted.
                map (solveIneq depth uS) ineqs)
              smallest = solvedInEqSmallestConstraint solvedIneq
          case smallest of
            (True,kW) -> do
              evs' <- maybe evs (:evs) <$> evMagic tcs ct deps kW (subToPred opts tcs k)
              simples deps subst evs' leqsG' xs eqs'
            _ -> simples deps subst evs leqsG (eq:xs) eqs'

    eqToLeq x y = [(x,y,True),(y,x,True)]
    substLeq s (x,y,b) = (substsSOP s x, substsSOP s y, b)

    isVarEqs (Left (_,S [P [V _]], S [P [V _]]), _) = True
    isVarEqs _ = False

    makeGivensSet otherEqs varEq
      = let (noMentionsV,mentionsV)   = partitionEithers
                                          (map (matchesVarEq varEq) otherEqs)
            (mentionsLHS,mentionsRHS) = partitionEithers mentionsV
            vS = swapVar varEq
            givensLHS = case mentionsLHS of
              [] -> []
              _  -> [mentionsLHS ++ ((varEq:mentionsRHS) ++ noMentionsV)]
            givensRHS = case mentionsRHS of
              [] -> []
              _  -> [mentionsRHS ++ (vS:mentionsLHS ++ noMentionsV)]
        in  case mentionsV of
              [] -> [noMentionsV]
              _  -> givensLHS ++ givensRHS

    matchesVarEq (Left (_, S [P [V v1]], S [P [V v2]]),_) r = case r of
      (Left (_,S [P [V v3]],_),_)
        | v1 == v3 -> Right (Left r)
        | v2 == v3 -> Right (Right r)
      (Left (_,_,S [P [V v3]]),_)
        | v1 == v3 -> Right (Left r)
        | v2 == v3 -> Right (Right r)
      (Right (_,(S [P [V v3]],_,_)),_)
        | v1 == v3 -> Right (Left r)
        | v2 == v3 -> Right (Right r)
      (Right (_,(_,S [P [V v3]],_)),_)
        | v1 == v3 -> Right (Left r)
        | v2 == v3 -> Right (Right r)
      _ -> Left r
    matchesVarEq _ _ = error "internal error"

    swapVar (Left (ct,S [P [V v1]], S [P [V v2]]),ps) =
      (Left (ct,S [P [V v2]], S [P [V v1]]),ps)
    swapVar _ = error "internal error"

    findFirstSimpliedWanted (Impossible e)   _  = Impossible e
    findFirstSimpliedWanted (Simplified evs) s2
      | any (isWanted . ctEvidence . snd . fst) evs
      = Simplified evs
      | otherwise
      = s2

-- If we allow negated numbers we simply do not emit the inequalities
-- derived from the subtractions that are converted to additions with a
-- negated operand
subToPred :: Opts -> LookedUpTyCons -> [(Type, Type)] -> [PredType]
subToPred Opts{..} tcs
  | negNumbers = const []
  | otherwise  =
    -- Given 'a - b', require 'b <= a'.
    map (\ (a, b) -> mkLEqNat tcs b a)

-- | Extract all Nat equality and inequality constraints from another constraint.
toNatEquality :: LookedUpTyCons -> TyConSubst -> Ct -> [(Either NatEquality NatInEquality,[(Type,Type)])]
toNatEquality tcs givensTyConSubst ct0
  | Just ((x,y), mbLTE) <- isNatRel tcs givensTyConSubst pred0
  , let
      (x',k1) = runWriter (normaliseNat x)
      (y',k2) = runWriter (normaliseNat y)
      ks      = k1 ++ k2
  = case mbLTE of
      Nothing ->
        -- Equality constraint: x ~ y
        [(Left (ct0, x', y'), ks)]
      Just b ->
        -- Inequality constraint: (x <=? y) ~ b
        [(Right (ct0, (x', y', b)), ks)]
  | otherwise
  = case classifyPredType pred0 of
      EqPred NomEq t1 t2
        -> goNomEq t1 t2
      _ -> []
  where
    pred0 = ctPred ct0
    -- x ~ y
    goNomEq lhs rhs
      -- Recur into a TyCon application for TyCons that we **do not** rewrite,
      -- e.g. peek inside the Maybe in 'Maybe (x + y) ~ Maybe (y + x)'.
      | Just tcApps1 <- splitTyConApp_upTo givensTyConSubst lhs
      , Just tcApps2 <- splitTyConApp_upTo givensTyConSubst rhs
      , let tcAppsMap1 = listToUniqMap $ NE.toList tcApps1
            tcAppsMap2 = listToUniqMap $ NE.toList tcApps2
            tcAppPairs = intersectUniqMap_C (,) tcAppsMap1 tcAppsMap2
      , (tc, (xs, ys)):_ <- nonDetUniqMapToList tcAppPairs
      , not $ tc `elem` [typeNatAddTyCon, typeNatSubTyCon, typeNatMulTyCon, typeNatExpTyCon]
      , let subs = filter (not . uncurry eqType) (zip xs ys)
      = concatMap (uncurry rewrite) subs
      | otherwise
      = rewrite lhs rhs

    rewrite x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      = [(Left (ct0,x',y'),k1 ++ k2)]
      | otherwise
      = []

    isNatKind :: Kind -> Bool
    isNatKind = (`eqType` natKind)

unifyItemToPredType :: CoreUnify -> PredType
unifyItemToPredType ui = mkEqPredRole Nominal ty1 ty2
  where
    ty1 = case ui of
            SubstItem {..} -> mkTyVarTy siVar
            UnifyItem {..} -> reifySOP siLHS
    ty2 = case ui of
            SubstItem {..} -> reifySOP siSOP
            UnifyItem {..} -> reifySOP siRHS

evSubtPreds :: CtLoc -> [PredType] -> TcPluginM Solve [Ct]
evSubtPreds loc = mapM (fmap mkNonCanonical . newWanted loc)

evMagic :: LookedUpTyCons -> Ct -> [Coercion] -> Set CType -> [PredType] -> TcPluginM Solve (Maybe ((EvTerm, Ct), [Ct]))
evMagic tcs ct deps knW preds = do
  holeWanteds <- evSubtPreds (ctLoc ct) preds
  knWanted <- mapM (mkKnWanted (ctLoc ct)) (toList knW)
  let newWant = knWanted ++ holeWanteds
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 ->
      let ctEv = mkPluginUnivCo "ghc-typelits-natnormalise" Nominal deps t1 t2
      in return (Just ((EvExpr (Coercion ctEv), ct),newWant))
    IrredPred p ->
      let t1 = mkTyConApp (c0TyCon tcs) []
          co = mkPluginUnivCo "ghc-typelits-natnormalise" Representational deps t1 p
          dcApp = evDataConApp (c0DataCon tcs) [] []
       in return (Just ((EvExpr $ evCast dcApp co, ct),newWant))
    _ -> return Nothing

mkKnWanted
  :: CtLoc
  -> CType
  -> TcPluginM Solve Ct
mkKnWanted loc (CType ty) = do
  kc_clas <- tcLookupClass knownNatClassName
  let kn_pred = mkClassPred kc_clas [ty]
  wantedCtEv <- newWanted loc kn_pred
  return $ mkNonCanonical wantedCtEv
