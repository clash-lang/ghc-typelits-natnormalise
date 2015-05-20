{-# LANGUAGE CPP             #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Copyright  :  (C) 2015, University of Twente
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
-}
module GHC.TypeLits.Normalise
  ( plugin )
where

-- external
import Data.IORef (IORef, newIORef,readIORef, modifyIORef)
import Data.List  (intersect)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set   (Set)
import qualified  Data.Set as Set

-- GHC API
import Bag        (bagToList)
import Coercion   (Role (Nominal), mkUnivCo)
import FastString (fsLit)
import Outputable (Outputable (..), (<+>), ($$), empty, text)
import Plugins    (Plugin (..), defaultPlugin)
import TcEvidence (EvBind (..), EvBindsVar (..), EvTerm (EvCoercion),
                   TcCoercion (..), evBindMapBinds, evVarsOfTerm)
import TcPluginM  (TcPluginM, getEnvs, tcPluginIO, tcPluginTrace,
                   unsafeTcPluginTcM, zonkCt)
import TcRnTypes  (Ct, CtEvidence (..), CtLoc, CtOrigin, Implication (..),
                   TcLclEnv (tcl_lie, tcl_loc), TcPlugin(..), TcPluginResult(..),
                   WantedConstraints (..), ctEvidence, ctEvPred, ctPred, ctLocEnv,
                   ctLoc, ctLocOrigin, isGiven, isWanted, mkNonCanonical)
import TcSMonad   (newGivenEvVar, newWantedEvVarNC, runTcS)
import TcType     (mkEqPred, typeKind)
import Type       (EqRel (NomEq), Kind, PredTree (EqPred), PredType, Type,
                   TyVar, classifyPredType, mkTyVarTy)
import TysWiredIn (typeNatKind)
import VarSet     (mkVarSet,minusVarSet,isEmptyVarSet,varSetElems)

-- internal
import GHC.Extra.Instances () -- Ord instance for Ct
import GHC.TypeLits.Normalise.Unify

-- workaround for https://ghc.haskell.org/trac/ghc/ticket/10301
import Control.Monad (unless)
import StaticFlags   (initStaticOpts, v_opt_C_ready)

-- | To use the plugin, add
--
-- @
-- {\-\# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise \#-\}
-- @
--
-- To the header of your file.
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = const $ Just normalisePlugin }

normalisePlugin :: TcPlugin
normalisePlugin = tracePlugin "ghc-typelits-natnormalise"
  TcPlugin { tcPluginInit  = tcPluginIO $ newIORef Set.empty
           , tcPluginSolve = decideEqualSOP
           , tcPluginStop  = const (return ())
           }

decideEqualSOP :: IORef (Set Ct) -> [Ct] -> [Ct] -> [Ct]
               -> TcPluginM TcPluginResult
decideEqualSOP _ _givens _deriveds []      = return (TcPluginOk [] [])
decideEqualSOP discharged givens  _deriveds wanteds = do
    -- GHC 7.10.1 puts deriveds with the wanteds, so filter them out
    let wanteds' = filter (isWanted . ctEvidence) wanteds
    let unit_wanteds = mapMaybe toNatEquality wanteds'
    case unit_wanteds of
      [] -> return (TcPluginOk [] [])
      _  -> do
        unit_givens <- mapMaybe toNatEquality <$> mapM zonkCt givens
        (solvedDists,disprovenDists) <- solvedDischarged discharged
        sr <- simplifyNats solvedDists disprovenDists (unit_givens ++ unit_wanteds)
        tcPluginTrace "normalised" (ppr sr)
        case sr of
          Simplified subst evs -> do
            let solved     = filter (isWanted . ctEvidence . snd) evs
            -- Create new wanted constraints
            let newWanteds = filter (isWanted . ctEvidence . siNote) subst
            discharedWanteds <- tcPluginIO (readIORef discharged)
            let existingWanteds = wanteds' ++ (Set.toList discharedWanteds)
            newWantedConstraints <- catMaybes <$>
                                    mapM (substItemToCt existingWanteds) newWanteds
            -- update set of discharged wanteds
            tcPluginIO (modifyIORef discharged (Set.union (Set.fromList newWantedConstraints)))
            -- return
            return (TcPluginOk solved newWantedConstraints)
          Impossible eq  -> return (TcPluginContradiction [fromNatEquality eq])

solvedDischarged :: IORef (Set Ct) -- ^ Discharged wanteds
                 -> TcPluginM ([Ct],[Ct]) -- ^ Solved discharged wanteds
solvedDischarged dischargedR = do
  -- Get the disproved discharged wanteds
  (_,lclEnv) <- getEnvs
  lies       <- tcPluginIO (readIORef (tcl_lie lclEnv))
  let insols = bagToList $ wc_insol lies
  discharged <- Set.toList <$> tcPluginIO (readIORef dischargedR)
  let disproven = discharged `intersect` insols

  -- get the proven discharged wanteds
  let implcs = bagToList (wc_impl lies)
      bnds   = map ic_binds implcs
  maps <- mapM ((\(EvBindsVar ref _) -> tcPluginIO $ readIORef ref)) bnds
  let vars  = concatMap (bagToList . evBindMapBinds) maps
      vars' = map (\v -> (v,isClosedEvBind vars v)) vars
      closedVars = map ((\(EvBind v _) -> v) . fst) $ filter snd vars'
      solved = filter ((`elem` closedVars) . ctev_evar . ctEvidence) discharged
  tcPluginTrace ("solvedDischarged " ++ show (length vars)) (ppr vars')

  return (solved,disproven)

isClosedEvBind :: [EvBind]
               -> EvBind
               -> Bool
isClosedEvBind ebs (EvBind _ t)
    | isEmptyVarSet vs = True
    | not (isEmptyVarSet (vs `minusVarSet` (mkVarSet evs))) = False
    | otherwise  = all (isClosedEvBind ebs) used
  where
    vs   = evVarsOfTerm t
    vs'  = varSetElems vs
    evs  = map (\(EvBind v' _) -> v') ebs
    used = filter (\(EvBind v' _) -> v' `elem` vs') ebs

substItemToCt :: [Ct] -- ^ Existing wanteds wanted
              -> UnifyItem TyVar Type Ct
              -> TcPluginM (Maybe Ct)
substItemToCt existingWanteds si
  | isGiven (ctEvidence ct)
  = Just <$> newSimpleGiven loc predicate (ty1,ty2)

  | predicate  `notElem` wantedPreds
  , predicateS `notElem` wantedPreds
  = Just <$> newSimpleWanted loc predicate

  | otherwise
  = return Nothing
  where
    predicate   = mkEqPred ty1 ty2
    predicateS  = mkEqPred ty2 ty1
    wantedPreds = map ctPred existingWanteds

    ty1       = case si of
                  (SubstItem {..}) -> mkTyVarTy siVar
                  (UnifyItem {..}) -> reifySOP siLHS
    ty2       = case si of
                  (SubstItem {..}) -> reifySOP siSOP
                  (UnifyItem {..}) -> reifySOP siRHS
    ct        = siNote si
    loc       = ctLoc ct

type NatEquality = (Ct,CoreSOP,CoreSOP)

fromNatEquality :: NatEquality -> Ct
fromNatEquality (ct, _, _) = ct

data SimplifyResult
  = Simplified CoreUnify [(EvTerm,Ct)]
  | Impossible NatEquality

instance Outputable SimplifyResult where
  ppr (Simplified subst evs) = text "Simplified" $$ ppr subst $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

simplifyNats :: [Ct] -- ^ Solved discharged wanteds
             -> [Ct] -- ^ Disproven discharged wanteds
             -> [NatEquality]
             -> TcPluginM SimplifyResult
simplifyNats solved disproven eqs =
    tcPluginTrace "simplifyNats" (ppr eqs) >> simples [] [] [] eqs
  where
    simples :: CoreUnify -> [Maybe (EvTerm, Ct)] -> [NatEquality]
            -> [NatEquality] -> TcPluginM SimplifyResult
    simples subst evs _xs [] = return (Simplified subst (catMaybes evs))
    simples subst evs xs (eq@(ct,u,v):eqs') = do
      ur <- unifyNats ct (substsSOP subst u) (substsSOP subst v)
      tcPluginTrace "unifyNats result" (ppr ur)
      case ur of
        Win         -> simples subst (((,) <$> evMagic ct <*> pure ct):evs) []
                               (xs ++ eqs')
        Lose        -> return (Impossible eq)
        Draw []     -> simples subst evs (eq:xs) eqs'
        Draw subst' -> simples (substsSubst subst' subst ++ subst')
                               (((,) <$> evMagic ct <*> pure ct):evs)
                               [] (xs ++ eqs')
        --Draw subst' -> do alreadySolved <- unifiersSolved solved disproven subst'
        --                  case alreadySolved of
        --                    Win -> simples (substsSubst subst' subst ++ subst')
        --                                   (((,) <$> evMagic ct <*> pure ct):evs)
        --                                   [] (xs ++ eqs')
        --                    Lose -> return (Impossible eq)
        --                    _    -> simples (substsSubst subst' subst ++ subst')
        --                                    evs [eq] (xs ++ eqs')

unifiersSolved :: [Ct]      -- ^ Solved wanted contraints
               -> [Ct]      -- ^ Disproven wanted constraints
               -> CoreUnify -- ^ List of derived unifiers
               -> TcPluginM UnifyResult
unifiersSolved solved disproven subst = do
    wantedConstraintsS <- catMaybes <$>
                          mapM (substItemToCt solved) wantedUnifiers
    wantedConstraintsD <- catMaybes <$>
                          mapM (substItemToCt disproven) wantedUnifiers
    tcPluginTrace "unifiersSolved" (text "solved:" <+> ppr solved $$
                                    text "disproven:" <+> ppr disproven $$
                                    text "subst:" <+> ppr subst $$
                                    text "wantedS:" <+> ppr wantedConstraintsS $$
                                    text "wantedD:" <+> ppr wantedConstraintsD)

    if (length wantedConstraintsD < length wantedUnifiers)
       then return Lose
       else if (null wantedConstraintsS)
               then return Win
               else return (Draw [])
  where
    wantedUnifiers = filter (isWanted . ctEvidence . siNote) subst

-- Extract the Nat equality constraints
toNatEquality :: Ct -> Maybe NatEquality
toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      | isNatKind (typeKind t1) || isNatKind (typeKind t1)
      -> Just (ct,normaliseNat t1,normaliseNat t2)
    _ -> Nothing
  where
    isNatKind :: Kind -> Bool
    isNatKind = (== typeNatKind)

-- Utils
newSimpleWanted :: CtLoc -> PredType -> TcPluginM Ct
newSimpleWanted loc p = do
  (ev,_) <- unsafeTcPluginTcM $ runTcS
                              $ newWantedEvVarNC loc p
  let ct  = mkNonCanonical ev
      loc = tcl_loc (ctLocEnv (ctLoc ct))
  tcPluginTrace "newSimpleWanted" (ppr ct $$ ppr loc)
  return ct

newSimpleGiven :: CtLoc -> PredType -> (Type,Type) -> TcPluginM Ct
newSimpleGiven loc predicate (ty1,ty2)= do
  (ev,_) <- unsafeTcPluginTcM $ runTcS
                              $ newGivenEvVar loc
                                  (predicate
                                  ,evByFiat "ghc-typelits-natnormalise" (ty1, ty2)
                                  )
  return (mkNonCanonical ev)

evMagic :: Ct -> Maybe EvTerm
evMagic ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> Just (evByFiat "ghc-typelits-natnormalise_magic" (t1, t2))
    _                  -> Nothing

evByFiat :: String -> (Type, Type) -> EvTerm
evByFiat name (t1,t2) = EvCoercion $ TcCoercion
                      $ mkUnivCo (fsLit name) Nominal t1 t2

tracePlugin :: String -> TcPlugin -> TcPlugin
tracePlugin s TcPlugin{..} = TcPlugin { tcPluginInit  = traceInit
                                      , tcPluginSolve = traceSolve
                                      , tcPluginStop  = traceStop
                                      }
  where
    traceInit    = do -- workaround for https://ghc.haskell.org/trac/ghc/ticket/10301
                      initializeStaticFlags
                      tcPluginTrace ("tcPluginInit " ++ s) empty >> tcPluginInit
    traceStop  z = do -- workaround for https://ghc.haskell.org/trac/ghc/ticket/10301
                      initializeStaticFlags
                      tcPluginTrace ("tcPluginStop " ++ s) empty >> tcPluginStop z

    traceSolve z given derived wanted = do
        -- workaround for https://ghc.haskell.org/trac/ghc/ticket/10301
        initializeStaticFlags
        tcPluginTrace ("tcPluginSolve start " ++ s)
                          (text "given   =" <+> ppr given
                        $$ text "derived =" <+> ppr derived
                        $$ text "wanted  =" <+> ppr wanted)
        r <- tcPluginSolve z given derived wanted
        case r of
          TcPluginOk solved new     -> tcPluginTrace ("tcPluginSolve ok " ++ s)
                                           (text "solved =" <+> ppr solved
                                         $$ text "new    =" <+> ppr new)
          TcPluginContradiction bad -> tcPluginTrace ("tcPluginSolve contradiction " ++ s)
                                           (text "bad =" <+> ppr bad)
        return r

-- workaround for https://ghc.haskell.org/trac/ghc/ticket/10301
initializeStaticFlags :: TcPluginM ()
initializeStaticFlags = tcPluginIO $ do
  r <- readIORef v_opt_C_ready
  unless r initStaticOpts
