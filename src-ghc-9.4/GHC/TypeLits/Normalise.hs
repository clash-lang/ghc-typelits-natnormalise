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
{-# LANGUAGE TemplateHaskellQuotes #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Control.Arrow (second)
import Control.Monad ((<=<), forM)
import Control.Monad.Trans.Writer.Strict
import Data.Either (partitionEithers, rights)
import Data.IORef
import Data.List (intersect, partition, stripPrefix, find)
import Data.Maybe (mapMaybe, catMaybes)
import Data.Set (Set, empty, toList, notMember, fromList, union)
import Text.Read (readMaybe)
import qualified Data.Type.Ord
import qualified GHC.TypeError

import GHC.TcPluginM.Extra (tracePlugin, newGiven, newWanted)

-- GHC API
import GHC.Builtin.Names (knownNatClassName, eqTyConKey, heqTyConKey, hasKey)
import GHC.Builtin.Types (promotedFalseDataCon, promotedTrueDataCon)
import GHC.Builtin.Types.Literals
  (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon, typeNatSubTyCon)
import GHC.Builtin.Types (naturalTy, cTupleDataCon, cTupleTyCon)
import GHC.Builtin.Types.Literals (typeNatCmpTyCon)
import GHC.Core (Expr (..))
import GHC.Core.Class (className)
import GHC.Core.Coercion (Role (..), mkUnivCo)
import GHC.Core.DataCon (dataConWrapId)
import GHC.Core.Predicate
  (EqRel (NomEq), Pred (EqPred, IrredPred), classifyPredType, mkClassPred,
   mkPrimEqPred, isEqPred, isEqPrimPred, getClassPredTys_maybe)
import GHC.Core.TyCo.Rep (Type (..), UnivCoProvenance (..))
import GHC.Core.TyCon (TyCon)
#if MIN_VERSION_ghc(9,6,0)
import GHC.Core.Type
  (Kind, PredType, mkTyVarTy, tyConAppTyCon_maybe, typeKind, mkTyConApp)
import GHC.Core.TyCo.Compare
  (eqType)
#else
import GHC.Core.Type
  (Kind, PredType, eqType, mkTyVarTy, tyConAppTyCon_maybe, typeKind, mkTyConApp)
#endif
import GHC.Data.IOEnv (getEnv)
import GHC.Driver.Plugins (Plugin (..), defaultPlugin, purePlugin)
import GHC.Plugins (thNameToGhcNameIO, HscEnv (hsc_NC))
import GHC.Tc.Plugin
  (TcPluginM, tcLookupClass, tcPluginTrace, tcPluginIO, newEvVar)
import GHC.Tc.Plugin (tcLookupTyCon, unsafeTcPluginTcM)
import GHC.Tc.Types (TcPlugin (..), TcPluginSolveResult(..), Env (env_top))
import GHC.Tc.Types.Constraint
  (Ct, CtEvidence (..), CtLoc, TcEvDest (..), ctEvidence,
   ctLoc, ctLocSpan, isGiven, isWanted, mkNonCanonical, setCtLocSpan,
   isWantedCt, ctEvLoc, ctEvPred, ctEvExpr, emptyRewriterSet, setCtEvLoc)
import GHC.Tc.Types.Evidence (EvBindsVar, EvTerm (..), evCast, evId)
import GHC.Types.Unique.FM (emptyUFM)
import GHC.Utils.Outputable (Outputable (..), (<+>), ($$), text)
import GHC (Name)

-- template-haskell
import qualified Language.Haskell.TH as TH

-- internal
import GHC.TypeLits.Normalise.SOP
import GHC.TypeLits.Normalise.Unify hiding (subtractionToPred)

isEqPredClass :: PredType -> Bool
isEqPredClass ty = case tyConAppTyCon_maybe ty of
  Just tc -> tc `hasKey` eqTyConKey || tc `hasKey` heqTyConKey
  _ -> False

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
  , pluginRecompile = purePlugin
  }
 where
  parseArgument "allow-negated-numbers" = Just (\ opts -> opts { negNumbers = True })
  parseArgument (readMaybe <=< stripPrefix "depth=" -> Just depth) = Just (\ opts -> opts { depth })
  parseArgument _ = Nothing
  defaultOpts = Opts { negNumbers = False, depth = 5 }

data Opts = Opts { negNumbers :: Bool, depth :: Word }

normalisePlugin :: Opts -> TcPlugin
normalisePlugin opts = tracePlugin "ghc-typelits-natnormalise"
  TcPlugin { tcPluginInit    = lookupExtraDefs
           , tcPluginSolve   = decideEqualSOP opts
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop    = const (return ())
           }

type ExtraDefs = (IORef (Set CType), (TyCon,TyCon,TyCon))

lookupExtraDefs :: TcPluginM ExtraDefs
lookupExtraDefs = do
    ref <- tcPluginIO (newIORef empty)
    ordCond <- lookupTHName ''Data.Type.Ord.OrdCond >>= tcLookupTyCon
    leqT <- lookupTHName ''(Data.Type.Ord.<=) >>= tcLookupTyCon
    assertT <- lookupTHName ''GHC.TypeError.Assert >>= tcLookupTyCon
    return (ref, (leqT,assertT,ordCond))

lookupTHName :: TH.Name -> TcPluginM Name
lookupTHName th = do
    nc <- unsafeTcPluginTcM (hsc_NC . env_top <$> getEnv)
    res <- tcPluginIO $ thNameToGhcNameIO nc th
    maybe (fail $ "Failed to lookup " ++ show th) return res

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
  -> EvBindsVar
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginSolveResult

-- Simplification phase: Derives /simplified/ givens;
-- we can reduce given constraints like @Show (Foo (n + 2))@
-- to its normal form @Show (Foo (2 + n))@, which is eventually
-- useful in solving phase.
--
-- This helps us to solve /indirect/ constraints;
-- without this phase, we cannot derive, e.g.,
-- @IsVector UVector (Fin (n + 1))@ from
-- @Unbox (1 + n)@!
decideEqualSOP opts (gen'd,(leqT,_,_)) ev givens [] = do
    done <- tcPluginIO $ readIORef gen'd
    let reds =
          filter (\(_,(_,_,v)) -> null v || negNumbers opts) $
          reduceGivens opts leqT done givens
        newlyDone = map (\(_,(prd, _,_)) -> CType prd) reds
    tcPluginIO $
      modifyIORef' gen'd $ union (fromList newlyDone)
    newGivens <- forM reds $ \(origCt, (pred', evTerm, _)) ->
      mkNonCanonical' (ctLoc origCt) <$> newGiven ev (ctLoc origCt) pred' evTerm
    return (TcPluginOk [] newGivens)

-- Solving phase.
-- Solves in/equalities on Nats and simplifiable constraints
-- containing naturals.
decideEqualSOP opts (gen'd,tcs@(leqT,_,_)) ev givens wanteds = do
    let unit_wanteds = mapMaybe (toNatEquality tcs) wanteds
        nonEqs = filter ( not
                        . (\p -> isEqPred p || isEqPrimPred p)
                        . ctEvPred
                        . ctEvidence )
                 wanteds
    done <- tcPluginIO $ readIORef gen'd
    let redGs = reduceGivens opts leqT done givens
        newlyDone = map (\(_,(prd, _,_)) -> CType prd) redGs
    redGivens <- forM redGs $ \(origCt, (pred', evTerm, _)) ->
      mkNonCanonical' (ctLoc origCt) <$> newGiven ev (ctLoc origCt) pred' evTerm
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
          fmap (mkNonCanonical' (ctLoc ct)) . newWanted (ctLoc ct)
        tcPluginIO $
          modifyIORef' gen'd $ union (fromList newlyDone)
        let unit_givens = mapMaybe
                            (toNatEquality tcs)
                            givens
        sr <- simplifyNats opts leqT unit_givens unit_wanteds
        tcPluginTrace "normalised" (ppr sr)
        reds <- forM reducible_wanteds $ \(origCt,(term, ws, wDicts)) -> do
          wants <- evSubtPreds (ctLoc origCt) $ subToPred opts leqT ws
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

reduceGivens :: Opts -> TyCon -> Set CType -> [Ct] -> [(Ct, (Type, EvTerm, [PredType]))]
reduceGivens opts leqT done givens =
  let nonEqs =
        [ ct
        | ct <- givens
        , let ev = ctEvidence ct
              prd = ctEvPred ev
        , isGiven ev
        , not $ (\p -> isEqPred p || isEqPrimPred p || isEqPredClass p) prd
        ]
  in filter
      (\(_, (prd, _, _)) ->
        notMember (CType prd) done
      )
    $ mapMaybe
      (\ct -> (ct,) <$> tryReduceGiven opts leqT givens ct)
      nonEqs

tryReduceGiven
  :: Opts -> TyCon -> [Ct] -> Ct
  -> Maybe (PredType, EvTerm, [PredType])
tryReduceGiven opts leqT simplGivens ct = do
    let (mans, ws) =
          runWriter $ normaliseNatEverywhere $
          ctEvPred $ ctEvidence ct
        ws' = [ p
              | p <- subToPred opts leqT ws
              , all (not . (`eqType` p). ctEvPred . ctEvidence) simplGivens
              ]
    pred' <- mans
    return (pred', toReducedDict (ctEvidence ct) pred', ws')

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

reduceNatConstr :: [Ct] -> Ct -> TcPluginM (Maybe (EvTerm, [(Type, Type)], [Ct]))
reduceNatConstr givens ct =  do
  let pred0 = ctEvPred $ ctEvidence ct
      (mans, tests) = runWriter $ normaliseNatEverywhere pred0
  case mans of
    Nothing -> return Nothing
    Just pred' -> do
      case find ((`eqType` pred') .ctEvPred . ctEvidence) givens of
        -- No existing evidence found
        Nothing -> case getClassPredTys_maybe pred' of
          -- Are we trying to solve a class instance?
          Just (cls,_) | className cls /= knownNatClassName -> do
            -- Create new evidence binding for normalized class constraint
            evVar <- newEvVar pred'
            -- Bind the evidence to a new wanted normalized class constraint
            let wDict = mkNonCanonical
                          (CtWanted pred' (EvVarDest evVar) (ctLoc ct) emptyRewriterSet)
            -- Evidence for current wanted is simply the coerced binding for
            -- the new binding
                evCo = mkUnivCo (PluginProv "ghc-typelits-natnormalise")
                         Representational
                         pred' pred0
                ev = evId evVar `evCast` evCo
            -- Use newly created coerced wanted as evidence, and emit the
            -- normalized wanted as a new constraint to solve.
            return (Just (ev, tests, [wDict]))
          _ -> return Nothing
        -- Use existing evidence
        Just c  -> return (Just (toReducedDict (ctEvidence c) pred0, tests, []))

toReducedDict :: CtEvidence -> PredType -> EvTerm
toReducedDict ct pred' =
  let pred0 = ctEvPred ct
      evCo = mkUnivCo (PluginProv "ghc-typelits-natnormalise")
              Representational
              pred0 pred'
      ev = ctEvExpr ct
             `evCast` evCo
  in ev

data SimplifyResult
  = Simplified [((EvTerm,Ct),[Ct])]
  | Impossible (Either NatEquality NatInEquality)

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats
  :: Opts
  -- ^ Allow negated numbers (potentially unsound!)
  -> TyCon
  -- * TyCon of Data.Type.Ord.<=
  -> [(Either NatEquality NatInEquality,[(Type,Type)])]
  -- ^ Given constraints
  -> [(Either NatEquality NatInEquality,[(Type,Type)])]
  -- ^ Wanted constraints
  -> TcPluginM SimplifyResult
simplifyNats opts@Opts {..} leqT eqsG eqsW = do
    let eqsG1 = map (second (const ([] :: [(Type,Type)]))) eqsG
        (varEqs,otherEqs) = partition isVarEqs eqsG1
        fancyGivens = concatMap (makeGivensSet otherEqs) varEqs
    case varEqs of
      [] -> do
        let eqs = otherEqs ++ eqsW
        tcPluginTrace "simplifyNats" (ppr eqs)
        simples [] [] [] [] eqs
      _  -> do
        tcPluginTrace ("simplifyNats(backtrack: " ++ show (length fancyGivens) ++ ")")
                      (ppr varEqs)

        allSimplified <- forM fancyGivens $ \v -> do
          let eqs = v ++ eqsW
          tcPluginTrace "simplifyNats" (ppr eqs)
          simples [] [] [] [] eqs

        pure (foldr findFirstSimpliedWanted (Simplified []) allSimplified)
  where
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
          evs' <- maybe evs (:evs) <$> evMagic ct empty (subToPred opts leqT k)
          simples subst evs' leqsG [] (xs ++ eqs')
        Lose -> if null evs && null eqs'
                   then return (Impossible (fst eq))
                   else simples subst evs leqsG xs eqs'
        Draw [] -> simples subst evs [] (eq:xs) eqs'
        Draw subst' -> do
          evM <- evMagic ct empty (map unifyItemToPredType subst' ++
                                   subToPred opts leqT k)
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
          isG   = isGiven (ctEvidence ct)
          leqsG' | isG       = (x',y',b):leqsG
                 | otherwise = leqsG
          ineqs = concat [ leqsG
                         , map (substLeq subst) leqsG
                         , map snd (rights (map fst eqsG))
                         ]
      tcPluginTrace "unifyNats(ineq) results" (ppr (ct,u,u',ineqs))
      case runWriterT (isNatural u') of
        Just (True,knW)  -> do
          evs' <- maybe evs (:evs) <$> evMagic ct knW (subToPred opts leqT k)
          simples subst evs' leqsG' xs eqs'

        Just (False,_) | null k && not isG -> return (Impossible (fst eq))
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
              evs' <- maybe evs (:evs) <$> evMagic ct kW (subToPred opts leqT k)
              simples subst evs' leqsG' xs eqs'
            _ -> simples subst evs leqsG (eq:xs) eqs'

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
      | any (isWantedCt . snd . fst) evs
      = Simplified evs
      | otherwise
      = s2

-- If we allow negated numbers we simply do not emit the inequalities
-- derived from the subtractions that are converted to additions with a
-- negated operand
subToPred :: Opts -> TyCon -> [(Type, Type)] -> [PredType]
subToPred Opts{..} leqT
  | negNumbers = const []
  | otherwise  = map leq
  where
    leq (a,b) =
      let lhs = TyConApp leqT [naturalTy,b,a]
          rhs = TyConApp (cTupleTyCon 0) []
       in mkPrimEqPred lhs rhs

-- Extract the Nat equality constraints
toNatEquality :: (TyCon,TyCon,TyCon) -> Ct -> Maybe (Either NatEquality NatInEquality,[(Type,Type)])
toNatEquality (_,assertT,ordCond) ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      -> go t1 t2
    IrredPred p
      -> go2 p
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
      | tc == ordCond
      , [_,cmp,lt,eq,gt] <- xs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      , let ks      = k1 ++ k2
      = case tc' of
         _ | tc' == promotedTrueDataCon
           -> Just (Right (ct, (x', y', True)), ks)
         _ | tc' == promotedFalseDataCon
           -> Just (Right (ct, (x', y', False)), ks)
         _ -> Nothing
      | tc == assertT
      , tc' == (cTupleTyCon 0)
      , [] <- ys
      , [TyConApp ordCondTc zs, _] <- xs
      , ordCondTc == ordCond
      , [_,cmp,lt,eq,gt] <- zs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      , let ks      = k1 ++ k2
      = Just (Right (ct, (x', y', True)), ks)

    go x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      = Just (Left (ct,x',y'),k1 ++ k2)
      | otherwise
      = Nothing

    go2 (TyConApp tc ys)
      | tc == assertT
      , [TyConApp ordCondTc xs, _] <- ys
      , ordCondTc == ordCond
      , [_,cmp,lt,eq,gt] <- xs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      , let (x',k1) = runWriter (normaliseNat x)
      , let (y',k2) = runWriter (normaliseNat y)
      , let ks      = k1 ++ k2
      = Just (Right (ct, (x', y', True)), ks)

    go2 _ = Nothing

    isNatKind :: Kind -> Bool
    isNatKind = (`eqType` naturalTy)

unifyItemToPredType :: CoreUnify -> PredType
unifyItemToPredType ui = mkPrimEqPred ty1 ty2
  where
    ty1 = case ui of
            SubstItem {..} -> mkTyVarTy siVar
            UnifyItem {..} -> reifySOP siLHS
    ty2 = case ui of
            SubstItem {..} -> reifySOP siSOP
            UnifyItem {..} -> reifySOP siRHS

evSubtPreds :: CtLoc -> [PredType] -> TcPluginM [Ct]
evSubtPreds loc = mapM (fmap mkNonCanonical . newWanted loc)

evMagic :: Ct -> Set CType -> [PredType] -> TcPluginM (Maybe ((EvTerm, Ct), [Ct]))
evMagic ct knW preds = do
  holeWanteds <- evSubtPreds (ctLoc ct) preds
  knWanted <- mapM (mkKnWanted (ctLoc ct)) (toList knW)
  let newWant = knWanted ++ holeWanteds
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 ->
      let ctEv = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Nominal t1 t2
      in return (Just ((EvExpr (Coercion ctEv), ct),newWant))
    IrredPred p ->
      let t1 = mkTyConApp (cTupleTyCon 0) []
          co = mkUnivCo (PluginProv "ghc-typelits-natnormalise") Representational t1 p
          dcApp = evId (dataConWrapId (cTupleDataCon 0))
       in return (Just ((evCast dcApp co, ct),newWant))
    _ -> return Nothing

mkNonCanonical' :: CtLoc -> CtEvidence -> Ct
mkNonCanonical' origCtl ev =
  let ct_ls   = ctLocSpan origCtl
      ctl     = ctEvLoc  ev
  in mkNonCanonical (setCtEvLoc ev (setCtLocSpan ctl ct_ls))

mkKnWanted
  :: CtLoc
  -> CType
  -> TcPluginM Ct
mkKnWanted loc (CType ty) = do
  kc_clas <- tcLookupClass knownNatClassName
  let kn_pred = mkClassPred kc_clas [ty]
  wantedCtEv <- newWanted loc kn_pred
  let wanted' = mkNonCanonical' loc wantedCtEv
  return wanted'
