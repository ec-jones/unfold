{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unfold where

import GHC.Core.Multiplicity
import GHC.Core.Opt.Arity
import GHC.Plugins
import qualified GHC.Utils.Outputable as Outputable

-- | An expression with ordered free variables.
data Goal = Goal
  { goalFVs :: [Id],
    goalBody :: CoreExpr
  }

instance Outputable Goal where
  ppr (Goal xs body) =
    forAllLit <+> pprWithCommas ppr xs Outputable.<> dot <+> ppr body

-- | Check if two goals are alpha equivalent.
alphaEquiv :: (?scope :: InScopeSet) => Goal -> Goal -> Bool
alphaEquiv (Goal xs body) (Goal xs' body') =
  let ?scope = extendInScopeSetList ?scope (xs ++ xs')
   in let subst = mkOpenSubst ?scope (zip xs' (map Var xs))
       in eqExpr ?scope body (substExpr subst body')

-- | A narrowing tree of congruence/case analyses.
data Narrowing m k
  = LitLeaf Literal
  | CongNode DataCon [k]
  | CaseNode
      CoreExpr
      -- ^ Simplified expression /before/ case analysis.
      Id
      -- ^ Scrutinee
      [(DataCon, m (k, Subst))]
      -- ^ Case continuation
  deriving stock (Functor)

-- | Unfold a goal into a list of reachable goals.
unfold ::
  forall m.
  ( MonadUnique m,
    ?defns :: IdEnv CoreExpr,
    ?scope :: InScopeSet
  ) =>
  Goal ->
  m [Goal]
unfold goal = loop [goal] []
  where
    loop :: [Goal] -> [Goal] -> m [Goal]
    loop [] seen = pure seen
    loop (goal : goals) seen =
      case narrow goal of
        (pre, _)
          | any (alphaEquiv pre) seen -> loop goals seen
        (pre, LitLeaf lit) -> loop goals (pre : seen)
        (pre, CongNode con goals') -> loop (goals' ++ goals) (pre : seen)
        (pre, CaseNode _ x cases) -> do
          goals' <- mapM (\(_, m) -> fst <$> m) cases
          loop (goals' ++ goals) (pre : seen)

-- | Narrow a goal.
narrow ::
  forall m.
  ( MonadUnique m,
    ?defns :: IdEnv CoreExpr,
    ?scope :: InScopeSet
  ) =>
  Goal ->
  (Goal, Narrowing m Goal)
narrow (Goal xs expr) =
  let ?scope = ?scope `extendInScopeSetList` xs
   in prePost (reduce expr [])
  where
    -- Rebuild the simplified goal and the result of narrowing.
    prePost :: Narrowing m Goal -> (Goal, Narrowing m Goal)
    prePost res@(LitLeaf lit) = (Goal xs (Lit lit), res)
    prePost res@(CongNode con subgoals) = (Goal xs (mkConApp con (map goalBody subgoals)), res)
    prePost res@(CaseNode pre _ _) = (Goal xs pre, res)

    -- Reduce an application, narrowing when appropriate.
    reduce :: CoreExpr -> [CoreArg] -> Narrowing m Goal
    reduce (Var x) args
      | Just con <- isDataConId_maybe x = do
          CongNode con [Goal xs arg | arg <- args]
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
        CongNode con subgoals
          | Just (Alt _ patVars rhs) <- findAlt (DataAlt con) alts -> do
              let conArgs = map goalBody subgoals
                  subst = mkOpenSubst ?scope ((x, mkConApp con conArgs) : zip patVars conArgs)
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
          (\(Goal ys res) -> Goal ys (Cast res g')) <$> reduce expr' args'
    reduce (Tick t expr) args = reduce expr args
    reduce (Type ty) args = pprPanic "Cannot narrow type!" (ppr ty)
    reduce (Coercion g) args = pprPanic "Cannot narrow coercion!" (ppr g)

-- | Expand the variable to a fresh instances of the constructor in the goal.
expand :: forall m. (MonadUnique m, ?scope :: InScopeSet) => Goal -> Id -> DataCon -> [Type] -> m (Goal, Subst)
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
