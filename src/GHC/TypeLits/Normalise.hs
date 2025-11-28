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

{-# LANGUAGE BangPatterns          #-}
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
  ( (<=<), unless )
import Control.Monad.Trans.Writer.Strict
  ( WriterT(runWriterT), runWriter )
import Data.Either
  ( rights, partitionEithers )
import Data.Foldable
import Data.List
  ( stripPrefix, partition )
import Data.Maybe
  ( mapMaybe, catMaybes, fromMaybe )
import Data.Traversable
  ( for )
import Text.Read
  ( readMaybe )

-- containers
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( elems, empty )
import Data.Map.Strict
  ( Map )
import qualified Data.Map.Strict as Map
  ( empty, insertWith, traverseWithKey )

-- ghc
import GHC.Builtin.Names
  ( knownNatClassName )
import GHC.Builtin.Types.Literals
  ( typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon, typeNatSubTyCon )
import GHC.Core.TyCon
  ( Injectivity (..), tyConInjectivityInfo, tyConArity )
import GHC.Utils.Misc
  ( filterByList )

-- ghc-tcplugin-api
import GHC.TcPlugin.API
import GHC.TcPlugin.API.TyConSubst
  ( TyConSubst, mkTyConSubst )
import GHC.Plugins
  ( Plugin(..), defaultPlugin, purePlugin )
import GHC.Utils.Outputable

-- ghc-typelits-natnormalise
import GHC.TypeLits.Normalise.Compat
import GHC.TypeLits.Normalise.SOP
  ( SOP(S), Product(P), Symbol(V) )
import GHC.TypeLits.Normalise.Unify

-- transformers
import Control.Monad.Trans.Class
  ( lift )
import Control.Monad.Trans.State.Strict
  ( StateT, evalStateT, get, modify )

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
    { tyCons :: LookedUpTyCons }

lookupExtraDefs :: TcPluginM Init ExtraDefs
lookupExtraDefs = do
  tcs <- lookupTyCons
  return $
    ExtraDefs
      { tyCons = tcs }

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
decideEqualSOP opts (ExtraDefs { tyCons = tcs }) givens [] =
   do
    let
      givensTyConSubst = mkTyConSubst givens
    (redGivens, _) <- reduceGivens False opts tcs givens

    tcPluginTrace "decideEqualSOP Givens {" $
      vcat [ text "givens:" <+> ppr givens ]

    -- Try to find contradictory Givens, to improve pattern match warnings.
    SimplifyResult { simplifiedWanteds, contradictions } <-
      simplifyNats opts tcs [] $
        concatMap (toNatEquality opts tcs givensTyConSubst) redGivens

    tcPluginTrace "decideEqualSOP Givens }" $
      vcat [ text "givens:" <+> ppr givens
           , text "simpls:" <+> ppr simplifiedWanteds
           , text "contra:" <+> ppr contradictions
           ]
    return $
      mkTcPluginSolveResult
        ( map fromNatEquality contradictions )
        [] -- no solved Givens
        [] -- no new Givens

-- Solving phase.
-- Solves in/equalities on Nats and simplifiable constraints
-- containing naturals.
decideEqualSOP opts (ExtraDefs { tyCons = tcs }) givens wanteds0 = do
    deriveds <- askDeriveds
    let wanteds = if null wanteds0
                  then []
                  else wanteds0 ++ deriveds
        givensTyConSubst = mkTyConSubst givens
        unit_wanteds0 = concatMap (toNatEquality opts tcs givensTyConSubst) wanteds
        nonEqs = filter ( not
                        . (\p -> isEqPred p || isEqClassPred p)
                        . ctEvPred
                        . ctEvidence )
                 wanteds

    (redGivens, negWanteds) <- reduceGivens True opts tcs givens
    reducible_wanteds
      <- catMaybes <$> mapM (\ct -> fmap (ct,) <$>
                                    reduceNatConstr redGivens ct)
                            nonEqs

    tcPluginTrace "decideEqualSOP Wanteds {" $
       vcat [ text "givens:" <+> ppr givens
            , text "new reduced givens:" <+> ppr redGivens
            , text $ replicate 80 '-'
            , text "wanteds:" <+> ppr wanteds
            , text "unit_wanteds:" <+> ppr unit_wanteds0
            , text "reducible_wanteds:" <+> ppr reducible_wanteds
            ]
    if null unit_wanteds0 && null reducible_wanteds
    then return $ TcPluginOk [] []
    else do
        -- Since reducible Wanteds also can have some negation/subtraction
        -- subterms, we have to make sure appropriate inequalities to hold.
        -- Here, we generate such additional inequalities for reduction
        -- that is to be added to new [W]anteds.
        let mkNegWanted ( CType wtdPred ) loc = mkNonCanonical <$> newWanted loc wtdPred
        ineqForRedWants <- Map.traverseWithKey mkNegWanted negWanteds
        let unit_givens = concatMap (toNatEquality opts tcs givensTyConSubst) redGivens
            unit_wanteds = unit_wanteds0 ++ concatMap (toNatEquality opts tcs givensTyConSubst) ineqForRedWants
        sr@SimplifyResult{simplifiedWanteds, contradictions} <-
          simplifyNats opts tcs unit_givens unit_wanteds
        tcPluginTrace "normalised" (ppr sr)
        reds <- for reducible_wanteds $ \(origCt,(term, ws, wDicts)) -> do
          wants <- evSubtPreds (ctLoc origCt) $ subToPred opts tcs ws
          return ((term, origCt), wDicts ++ wants)
        let -- Only solve a Derived when there are Wanteds in play
            simpld1 = case filter (isWanted . ctEvidence . (\((_,x),_) -> x)) simplifiedWanteds ++ reds of
                        [] -> []
                        _  -> simplifiedWanteds
            (solved,newWanteds) = second concat (unzip $ simpld1 ++ reds)

        tcPluginTrace "decideEqualSOP Wanteds }" $
           vcat [ text "givens:" <+> ppr givens
                , text "new reduced givens:" <+> ppr redGivens
                , text "unit givens:" <+> ppr unit_givens
                , text $ replicate 80 '-'
                , text "wanteds:" <+> ppr wanteds
                , text "ineqForRedWants:" <+> ppr ineqForRedWants
                , text "unit_wanteds:" <+> ppr unit_wanteds
                , text "reducible_wanteds:" <+> ppr reducible_wanteds
                , text $ replicate 80 '='
                , text "solved:" <+> ppr solved
                , text "newWanteds:" <+> ppr newWanteds
                ]
        return $
          mkTcPluginSolveResult
            (map fromNatEquality contradictions)
            solved
            newWanteds

type NatEquality   = (Ct,CoreSOP,CoreSOP)
type NatInEquality = (Ct,(CoreSOP,CoreSOP,Bool))

reduceGivens :: Bool -- ^ allow generating new "non-negative" Wanteds
             -> Opts -> LookedUpTyCons
             -> [Ct]
             -> TcPluginM Solve ([Ct], Map CType CtLoc)
reduceGivens gen_wanteds opts tcs origGivens = go [] Map.empty origGivens
  where
    go rev_acc_gs acc_ws [] = return ( reverse rev_acc_gs, acc_ws )
    go rev_acc_gs acc_ws (g:gs) =
      case tryReduceGiven opts tcs origGivens g of
        Just ( pred', evExpr, ws )
          | gen_wanteds || null ws || negNumbers opts
          -> do
            let loc = ctLoc g
            g' <- mkNonCanonical <$> newGiven loc pred' evExpr
            let !acc' = foldl' (insertWanted loc) acc_ws ws
            go ( g' : rev_acc_gs ) acc' gs
        _ ->
          go ( g : rev_acc_gs ) acc_ws gs

    insertWanted :: CtLoc -> Map CType CtLoc -> Type -> Map CType CtLoc
    insertWanted loc acc w =
      Map.insertWith (\ _new old -> old) (CType w) loc acc

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
              , all (not . (`eqType` p) . ctEvPred . ctEvidence) simplGivens
              ]
        -- deps = unitDVarSet (ctEvId ct)
    (pred', deps) <- mans
    case classifyPredType pred' of
      EqPred _ l r
        | l `eqType` r
        -> Nothing
      _ -> return (pred', toReducedDict (ctEvidence ct) pred' deps, ws')

fromNatEquality :: Either NatEquality NatInEquality -> Ct
fromNatEquality (Left  (ct, _, _)) = ct
fromNatEquality (Right (ct, _))    = ct

reduceNatConstr :: [Ct] -> Ct -> TcPluginM Solve (Maybe (EvTerm, [(Type, Type)], [Ct]))
reduceNatConstr givens ct = do
  let pred0 = ctEvPred $ ctEvidence ct
      (mans, tests) = runWriter $ normaliseNatEverywhere pred0

      -- Even if we didn't rewrite the Wanted,
      -- we may still be able to solve it from a (rewritten) Given.
      (pred', deps') = fromMaybe (pred0, []) mans
  case find ((`eqType` pred') . ctEvPred . ctEvidence) givens of
    -- No existing evidence found
    Nothing
      | ClassPred cls _ <- classifyPredType pred'
      , className cls /= knownNatClassName

      -- We actually did do some rewriting/normalisation.
      , Just {} <- mans
      -> do
          -- Create new evidence binding for normalized class constraint
          wtdDictCt <- mkNonCanonical <$> newWanted (ctLoc ct) pred'
          -- Evidence for current wanted is simply the coerced binding for
          -- the new binding
          let evCo = mkPluginUnivCo "ghc-typelits-natnormalise"
                       Representational
                       deps'
                       pred' pred0
              ev = evCast (evId $ ctEvId wtdDictCt) evCo
          -- Use newly created coerced wanted as evidence, and emit the
          -- normalized wanted as a new constraint to solve.
          return (Just (EvExpr ev, tests, [wtdDictCt]))
      | otherwise
      -> return Nothing
    -- Use existing evidence
    Just c  -> return (Just (toReducedDict (ctEvidence c) pred0 deps', tests, []))

toReducedDict :: CtEvidence -> PredType -> [Coercion] -> EvTerm
toReducedDict ct pred' deps' =
  let pred0 = ctEvPred ct
      evCo = mkPluginUnivCo "ghc-typelits-natnormalise"
              Representational
              deps'
              pred0 pred'
      ev = evCast (ctEvExpr ct) evCo
  in EvExpr ev

data SimplifyResult
  = SimplifyResult
     { simplifiedWanteds :: [((EvTerm,Ct),[Ct])]
     -- ^ List of:
     --   * Tuple of:
     --     * Evidence for:
     --     * The solved Wanted
     --   * Preconditions (in the for of new Wanteds)
     , contradictions :: [Either NatEquality NatInEquality]
     -- ^ List of contradictions
     }

instance Outputable SimplifyResult where
  ppr (SimplifyResult { simplifiedWanteds, contradictions }) =
    text "SimplifyResult { simplified =" <+> ppr simplifiedWanteds
               <+> text ", impossible =" <+> ppr contradictions <+> text "}"

data NatCt
  = NatCt
  { predicate :: Either NatEquality NatInEquality
  -- ^ Predicate: either an equality or inequality
  , preconds :: [PredType]
  -- ^ Preconditions (in the form of inequalities encoded as PredTypes)
  , ctDeps :: [Coercion]
  -- ^ Coercion(s) from which the predicate is derived, needed so that evidence
  -- doesn't float above the coercions from which it is derived.
  }

instance Outputable NatCt where
  ppr (NatCt {predicate, preconds, ctDeps}) =
    text "NatCt { predicate = " <+> ppr predicate
      <+> text ", preconditions = " <+> ppr preconds
      <+> text ", dependencies = " <+> ppr ctDeps <+> text "}"

data SimplifyState
  = SimplifyState
  { stDeps :: [Coercion]
    -- ^ Coercions on which the simplified evidence depends, this needs to be
    -- kept around because sometimes we solving one constraint (which has a
    -- depedency) is used to solve another constraint
  , subst :: [CoreUnify]
    -- ^ Derived simplifications (i.e. b ~ c derived from (a + b) ~ (a + c)),
    -- and substitutions (i.e. n := 0 derived from y ^ n ~ 1)
  , evs :: [((EvTerm,Ct),[Ct])]
    -- ^ Collected evidence
  , leqsG :: [(CoreSOP,CoreSOP,Bool)]
    -- ^ Given inequalities
  , unsolved :: [NatCt]
    -- ^ Tried, but unsolved predicates. We keep them around in case we solve a
    -- new predicate which could lead to a substitution that enables a solve.
  }

emptySimplifyState :: SimplifyState
emptySimplifyState
  = SimplifyState
  { stDeps = []
  , subst = []
  , evs = []
  , leqsG = []
  , unsolved = []
  }

simplifyNats
  :: Opts
  -- ^ Allow negated numbers (potentially unsound!)
  -> LookedUpTyCons
  -> [NatCt]
  -- ^ Given constraints
  -> [NatCt]
  -- ^ Wanted constraints
  -> TcPluginM Solve SimplifyResult
simplifyNats Opts{depth} tcs eqsG eqsW = do
    let eqsG1 = map (\nCt -> nCt{preconds = []}) eqsG
        (varEqs, otherEqs) = partition (isVarEqs . predicate) eqsG1
        fancyGivens = concatMap (makeGivensSet otherEqs) varEqs
    case varEqs of
      [] -> do
        let eqs = otherEqs ++ eqsW
        tcPluginTrace "simplifyNats" (ppr eqs)
        evalStateT (simples eqs) emptySimplifyState
      _  -> do
        tcPluginTrace ("simplifyNats(backtrack: " ++ show (length fancyGivens) ++ ")")
                      (ppr varEqs)

        allSimplified <- for fancyGivens $ \v -> do
          let eqs = v ++ eqsW
          tcPluginTrace "simplifyNats" (ppr eqs)
          evalStateT (simples eqs) emptySimplifyState

        pure (foldr findFirstSimpliedWanted (SimplifyResult [] []) allSimplified)
  where
    simples ::
      [NatCt] ->
      StateT SimplifyState (TcPluginM Solve) SimplifyResult
    simples [] = do
      SimplifyState{evs} <- get
      return (SimplifyResult evs [])
    simples (eq@NatCt{predicate=(Left (ct,u,v)), preconds, ctDeps}:eqs) = do
      SimplifyState{stDeps, subst, evs, leqsG, unsolved} <- get
      let allDeps = stDeps ++ ctDeps

      let u' = substsSOP subst u
          v' = substsSOP subst v
      ur <- lift (unifyNats ct u' v')
      lift (tcPluginTrace "unifyNats result" (ppr ur))
      case ur of
        Win -> do
          -- Do note record "new" evidence for given constraints.
          unless (isGiven (ctEvidence ct)) $ do
            -- Only recorde evidence for wanted contstraints
            evM <- lift (evMagic tcs ct allDeps mempty preconds)
            lift $ tcPluginTrace "unifyNats Win" $
              vcat [ text "evM:" <+> ppr evM
                   , text "ct:" <+> ppr ct
                   ]
            modify (\s -> s {evs = maybe evs (:evs) evM})
          simples eqs
        Lose ->
          addContra (predicate eq) <$> simples eqs
        Draw [] -> do
          -- No progress made, add it to the "unsolved" list, in the hope we
          -- can make progress when we later find a new substitution
          modify (\s -> s {unsolved = eq:unsolved})
          simples eqs
        Draw unifications -> do -- We made some progress in the form of a unifier

          -- As the derived unifiers we record here can lead to solving another
          -- equation, we add it and its dependencies to the list of global
          -- dependencies which we use when creating new evidence
          let stDeps1 = ctEvCoercion (ctEvidence ct):allDeps
          -- We add apply the derived unification in the existing set of
          -- unification, and also add the derived unificaiton to the global
          -- state; to be used in solving later equations.
          let subst1 = substsSubst unifications subst ++ unifications
          if isGiven (ctEvidence ct) then do
            if null preconds then do
              -- We only record the unification derived from a given constraint
              -- when it has no preconditions in order for this unification to
              -- hold. The reason for that is that we can currently not record
              -- new Wanteds to be emitted at the end of the solve.
              modify (\s -> s { stDeps = stDeps1
                              , subst = subst1
                              , leqsG = eqToLeq u' v' ++ leqsG
                              , unsolved = []
                              })
              simples (unsolved ++ eqs)
            else
              simples eqs
          else do
            let allPreconds = map unifyItemToPredType unifications ++ preconds
            evM <- lift (evMagic tcs ct allDeps Set.empty allPreconds)
            case evM of
              Nothing ->
                simples eqs
              Just ev -> do
                -- We only record the unification derived from a wanted constraint
                -- when we can actually record evidence for a succesful solve.
                modify (\s -> s { stDeps = stDeps1
                                , subst = subst1
                                , evs = ev:evs
                                , unsolved = []
                                })
                simples (unsolved ++ eqs)

    simples (eq@NatCt{predicate=Right (ct,u@(x,y,b)), preconds, ctDeps}:eqs) = do
      SimplifyState{stDeps, subst, evs, leqsG, unsolved} <- get
      let u'    = substsSOP subst (subtractIneq u)
          x'    = substsSOP subst x
          y'    = substsSOP subst y
          uS    = (x',y',b)
          leqsG' | isGiven (ctEvidence ct) = (x',y',b):leqsG
                 | otherwise               = leqsG
          ineqs = concat [ leqsG
                         , map (substLeq subst) leqsG
                         , map snd (rights (map predicate eqsG))
                         ]
          allDeps = stDeps ++ ctDeps
      lift (tcPluginTrace "unifyNats(ineq) results" (ppr (ct,u,u',ineqs)))
      case runWriterT (isNatural u') of
        Just (True,knW)  -> do
          evs' <- maybe evs (:evs) <$> lift (evMagic tcs ct allDeps knW preconds)
          modify (\s -> s {evs = evs', leqsG = leqsG'})
          simples eqs

        Just (False,_) | null preconds ->
          addContra (predicate eq) <$> simples eqs
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
              evs' <- maybe evs (:evs) <$> lift (evMagic tcs ct allDeps kW preconds)
              modify (\s -> s { stDeps = allDeps
                              , evs = evs'
                              , leqsG = leqsG'
                              })
              simples eqs
            _ -> do
              modify (\s -> s {unsolved = eq:unsolved})
              simples eqs

    eqToLeq x y = [(x,y,True),(y,x,True)]
    substLeq s (x,y,b) = (substsSOP s x, substsSOP s y, b)

    isVarEqs (Left (_,S [P [V _]], S [P [V _]])) = True
    isVarEqs _ = False

    makeGivensSet :: [NatCt] -> NatCt -> [[NatCt]]
    makeGivensSet otherEqs varEq
      = let (noMentionsV,mentionsV)   = partitionEithers
                                          (map (matchesVarEq varEq) otherEqs)
            (mentionsLHS,mentionsRHS) = partitionEithers mentionsV
            vS = varEq {predicate = swapVar (predicate varEq)}
            givensLHS = case mentionsLHS of
              [] -> []
              _  -> [mentionsLHS ++ ((varEq:mentionsRHS) ++ noMentionsV)]
            givensRHS = case mentionsRHS of
              [] -> []
              _  -> [mentionsRHS ++ (vS:mentionsLHS ++ noMentionsV)]
        in  case mentionsV of
              [] -> [noMentionsV]
              _  -> givensLHS ++ givensRHS

    matchesVarEq :: NatCt
                 -> NatCt
                 -> Either NatCt (Either NatCt NatCt)
    matchesVarEq NatCt{predicate = Left (_, S [P [V v1]], S [P [V v2]])} r@(NatCt e _ _) =
      case e of
        Left (_,S [P [V v3]],_)
          | v1 == v3 -> Right (Left r)
          | v2 == v3 -> Right (Right r)
        Left (_,_,S [P [V v3]])
          | v1 == v3 -> Right (Left r)
          | v2 == v3 -> Right (Right r)
        Right (_,(S [P [V v3]],_,_))
          | v1 == v3 -> Right (Left r)
          | v2 == v3 -> Right (Right r)
        Right (_,(_,S [P [V v3]],_))
          | v1 == v3 -> Right (Left r)
          | v2 == v3 -> Right (Right r)
        _ -> Left r
    matchesVarEq _ _ = error "internal error"

    swapVar (Left (ct,S [P [V v1]], S [P [V v2]])) =
      Left (ct,S [P [V v2]], S [P [V v1]])
    swapVar _ = error "internal error"

    findFirstSimpliedWanted s1@(SimplifyResult {simplifiedWanteds, contradictions}) s2
      |  not (null contradictions)
      || any (isWanted . ctEvidence . snd . fst) simplifiedWanteds
      = s1
      | otherwise
      = s2

addContra :: Either NatEquality NatInEquality -> SimplifyResult -> SimplifyResult
addContra contra sr = sr { contradictions = contra : contradictions sr }

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
toNatEquality :: Opts -> LookedUpTyCons -> TyConSubst -> Ct -> [NatCt]
toNatEquality opts tcs givensTyConSubst ct0
  | Just (((x,y), mbLTE), cos0) <- isNatRel tcs givensTyConSubst pred0
  , let
      ((x', cos1),k1) = runWriter (normaliseNat x)
      ((y', cos2),k2) = runWriter (normaliseNat y)
      preds = subToPred opts tcs (k1 ++ k2)
  = case mbLTE of
      Nothing ->
        -- Equality constraint: x ~ y
        [NatCt (Left (ct0, x', y')) preds (cos0 ++ cos1 ++ cos2)]
      Just b ->
        -- Inequality constraint: (x <=? y) ~ b
        [NatCt (Right (ct0, (x', y', b))) preds (cos0 ++ cos1 ++ cos2)]
  | otherwise
  = case classifyPredType pred0 of
      EqPred NomEq t1 t2
        -> goNomEq t1 t2
      ClassPred kn [x]
        -- From [G] KnownNat blah, also produce [G] 0 <= blah
        -- See https://github.com/clash-lang/ghc-typelits-natnormalise/issues/94.
        | isGiven (ctEvidence ct0)
        , className kn == knownNatClassName
        , let ((x', cos0), ks) = runWriter (normaliseNat x)
        , let preds = subToPred opts tcs ks
        -> [NatCt (Right (ct0, (S [], x', True))) preds cos0]
      _ -> []
  where
    pred0 = ctPred ct0
    -- x ~ y
    goNomEq :: Type -> Type -> [NatCt]
    goNomEq lhs rhs
      -- Recur into a TyCon application for TyCons that we **do not** rewrite,
      -- e.g. peek inside the Maybe in 'Maybe (x + y) ~ Maybe (y + x)'.
      | Just (tc , xs) <- splitTyConApp_maybe lhs
      , Just (tc', ys) <- splitTyConApp_maybe rhs
      , tc == tc'
      , not $ tc `elem` [typeNatAddTyCon, typeNatSubTyCon, typeNatMulTyCon, typeNatExpTyCon]
      , let xys = zip xs ys
      -- Make sure not to recur into non-injective positions of type families,
      -- e.g. if we know 'F n ~ F m' that doesn't mean 'n ~ m'.
            subs  =
              filter (not . uncurry eqType) $
                case tyConInjectivityInfo tc of
                  Injective inj ->
                    filterByList (inj ++ repeat True) xys
                  _ -> drop (tyConArity tc) xys
      = concatMap (uncurry rewrite) subs
      | otherwise
      = rewrite lhs rhs

    rewrite :: Type -> Type -> [NatCt]
    rewrite x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let ((x', cos1),k1) = runWriter (normaliseNat x)
      , let ((y', cos2),k2) = runWriter (normaliseNat y)
      , let preds = subToPred opts tcs (k1 ++ k2)
      = [NatCt (Left (ct0,x',y')) preds (cos1 ++ cos2)]
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

evMagic ::
  -- | Known TyCon environment
  LookedUpTyCons ->
  -- | Constraint for which we are creating evidence
  Ct ->
  -- | Coercions in which the evidence depends
  [Coercion] ->
  -- | Types that we should be known to be a Natural
  Set CType ->
  -- | Inequalities that should hold
  [PredType] ->
  TcPluginM Solve (Maybe ((EvTerm, Ct), [Ct]))
evMagic tcs ct deps knW preds = do
  holeWanteds <- evSubtPreds (ctLoc ct) preds
  knWanted <- mapM (mkKnWanted (ctLoc ct)) (Set.elems knW)
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
