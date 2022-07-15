{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unfold where

import GHC.Core.Multiplicity
import GHC.Core.Opt.Arity
import GHC.Plugins
import GHC.Types.Unique.DSet
import qualified Data.List as List
import qualified GHC.Utils.Outputable as Outputable

-- | An expression with ordered free variables.
data Goal k = 
  Goal [Id] k
  deriving stock Functor

instance Outputable k => Outputable (Goal k) where
  ppr (Goal xs body) =
    forAllLit <+> pprWithCommas ppr xs Outputable.<> dot <+> ppr body

-- | Free variables in a goal.
goalFVs :: Goal k -> [Id]
goalFVs (Goal xs _) = xs

-- | Check if two goals are alpha equivalent.
alphaEquiv :: (?scope :: InScopeSet) => Goal CoreExpr -> Goal CoreExpr -> Bool
alphaEquiv (Goal xs body) (Goal xs' body') =
  let ?scope = extendInScopeSetList ?scope (xs ++ xs')
   in let subst = mkOpenSubst ?scope (zip xs' (map Var xs))
       in eqExpr ?scope body (substExpr subst body')

-- | A partial narrowing tree with at most one case analysis in each branch.
data Narrowing m k
  = LitLeaf Literal
  | CongNode DataCon [Narrowing m k]
  | CaseNode
      CoreExpr
      -- ^ Simplified expression /before/ case analysis.
      Id
      -- ^ Scrutinee
      [(DataCon, m (Goal k, Subst))]
      -- ^ Case continuation
  deriving stock Functor

-- | Reconstruct the goal before narrowing but after reduction.
preNarrowing :: Narrowing m k -> CoreExpr
preNarrowing (LitLeaf lit) = Lit lit
preNarrowing (CongNode con conArgs) = mkConApp con (map preNarrowing conArgs)
preNarrowing (CaseNode reduct _ _) = reduct

-- | Collect sub-goals from a partial narrowing tree.
subGoals :: Functor m => Narrowing m k -> [m (Goal k)]
subGoals (LitLeaf _) = []
subGoals (CongNode _ conArgs) = [ subGoal | conArg <- conArgs, subGoal <- subGoals conArg]
subGoals (CaseNode _ _ cases) = [ fmap fst subgoal | (_, subgoal) <- cases]

-- | Unfold a goal into a list of reachable goals.
unfold ::
  forall m.
  ( MonadUnique m,
    ?defns :: IdEnv CoreExpr,
    ?scope :: InScopeSet
  ) =>
  Goal CoreExpr ->
  m [Goal CoreExpr]
unfold goal = loop [goal] []
  where
    loop :: [Goal CoreExpr] -> [Goal CoreExpr] -> m [Goal CoreExpr]
    loop [] seen = pure seen
    loop (goal : goals) seen = do
      let narrowing = narrow goal
          reduct = preNarrowing narrowing
          goal' = Goal (goalFVs goal) reduct
      pprTraceM "Goal:" (ppr goal')

      if any (alphaEquiv goal') seen
        then loop goals seen
        else do
          case List.find (\x -> not (x `elementOfUniqDSet` freeVarsOf (freeVars reduct))) (goalFVs goal) of
            Nothing -> do
              goals' <- sequence (subGoals narrowing)
              loop (goals' ++ goals) (goal' : seen)
            Just x -> do
              let (tc, tcArgs) = splitTyConApp (idType x)
                  narrowing' = CaseNode reduct x [(dc, expand goal' x dc tcArgs) | dc <- tyConDataCons tc]
              goals' <- sequence (subGoals narrowing')
              loop (goals' ++ goals) (goal' : seen)

-- | Narrow a goal.
narrow ::
  forall m.
  ( MonadUnique m,
    ?defns :: IdEnv CoreExpr,
    ?scope :: InScopeSet
  ) =>
  Goal CoreExpr ->
  Narrowing m CoreExpr
narrow (Goal xs expr) =
  let ?scope = ?scope `extendInScopeSetList` xs
   in reduce expr []
  where
    -- Reduce an application, narrowing when appropriate.
    reduce :: CoreExpr -> [CoreArg] -> Narrowing m CoreExpr
    reduce (Var x) args
      | Just con <- isDataConId_maybe x = do
          CongNode con [ reduce arg [] | arg <- args, isValArg arg]
      | x `elem` xs = do
          let (tc, tcArgs) = splitTyConApp (idType x)
              goal = Goal xs (mkApps (Var x) args)
           in CaseNode (Var x) x [(dc, expand goal x dc tcArgs) | dc <- tyConDataCons tc]
      | otherwise =
          case lookupVarEnv ?defns x of
            Nothing -> pprPanic "Variable not in scope!" (ppr x)
            Just defn -> reduce defn args
    reduce (Lit lit) _ = LitLeaf lit
    reduce (App fun arg) args = reduce fun (arg : args)
    reduce expr@(Lam x body) [] =
      pprPanic "Higher-order goals are not supported!" (ppr expr)
    reduce (Lam x body) (arg : args) =
      let subst = mkOpenSubst ?scope [(x, arg)]
       in reduce (substExpr subst body) args
    reduce (Let (NonRec x defn) body) args =
      let subst = mkOpenSubst ?scope [(x, defn)]
       in reduce (substExpr subst body) args
    reduce (Let (Rec binds) body) args =
      let subst = mkOpenSubst ?scope [(x, Let (Rec binds) defn) | (x, defn) <- binds]
       in reduce (substExpr subst body) args
    reduce expr@(Case scrut x ty alts) args =
      case reduce scrut [] of
        LitLeaf lit
          | Just (Alt _ _ rhs) <- findAlt (LitAlt lit) alts -> reduce rhs args
          | otherwise -> pprPanic "Case expression is non-exhaustive!" (ppr expr)
        CongNode con (map preNarrowing -> conArgs)
          | Just (Alt _ patVars rhs) <- findAlt (DataAlt con) alts -> do
              let subst = mkOpenSubst ?scope ((x, mkConApp con conArgs) : zip patVars conArgs)
               in reduce (substExpr subst rhs) args
          | otherwise -> pprPanic "Case expression is non-exhaustive!" (ppr expr)
        CaseNode scrut' y cases ->
          CaseNode
            (Case scrut' x ty alts)
            y
            [ ( dc,
                fmap
                  ( \(Goal ys scrut', subst) ->
                      (Goal ys (Case scrut' x ty (substAlt (subst `delBndr` x) <$> alts)), subst)
                  )
                  k
              )
              | (dc, k) <- cases
            ]
    reduce expr@(Cast expr' g) args =
      case pushCoArgs g args of
        Nothing -> pprPanic "Cannot push coercion args!" (ppr (mkApps expr args))
        Just (args', MRefl) ->
          reduce expr' args'
        Just (args', MCo g') -> do
          (`Cast` g') <$> reduce expr' args'
    reduce (Tick t expr) args = reduce expr args
    reduce (Type ty) args = pprPanic "Cannot narrow type!" (ppr ty)
    reduce (Coercion g) args = pprPanic "Cannot narrow coercion!" (ppr g)

-- | Expand the variable to a fresh instances of the constructor in the goal.
expand :: forall m. (MonadUnique m, ?scope :: InScopeSet) => Goal CoreExpr -> Id -> DataCon -> [Type] -> m (Goal CoreExpr, Subst)
expand goal@(Goal xs expr) x con tyargs = do
  us <- mapM freshId (dataConInstArgTys con tyargs)
  let subst = mkOpenSubst ?scope [(x, mkConApp con (map Var us))]
  case break (== x) xs of
    (ys, _ : zs) -> pure (Goal (ys ++ us ++ zs) (substExpr subst expr), subst)
    noX -> pprPanic "Cannot expand variable!" (ppr (x, goal))
  where
    freshId :: Scaled Type -> m Id
    freshId (Scaled mult ty) = do
      unique <- getUniqueM
      let name = mkInternalName unique (mkVarOcc ("_" ++ show unique)) (UnhelpfulSpan UnhelpfulGenerated)
      pure (mkLocalId name mult ty)

-- | Apply a substitution to a case alternative.
substAlt :: Subst -> CoreAlt -> CoreAlt
substAlt subst (Alt con bndrs rhs) =
  let (subst', bndrs') = substBndrs subst bndrs
   in Alt con bndrs' (substExpr subst' rhs)
