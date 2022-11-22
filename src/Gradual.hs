module Gradual (
    check
  , checkGoal
) where

import Language
import Checker

checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)
checkGoal env s@(Forall _ typ) = check (instantiateGoal s env) typ

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check env typ (Hole _ _) =
  return $ Hole typ $ Spec env typ
check env typ (Lam _ x e) = 
  case typ of
    (TArrow a b) -> Lam (a --> b) x <$> check (extend x a env) b e
    _ -> throwError "Expected arrow type"
check env typ e = do
  t' <- synth env e
  addConstraint $ Constraint env (annotation t') typ
  solveAll
  return e

-- Infer type
synth :: MonadND m => Environment -> Term Type -> Checker m (Term Type)
synth env (Hole _ _) = do
  t <- instantiate holeType 
  return $ Hole t $ Spec env t
synth env (App _ f x) = do
  f' <- synth env f 
  case annotation f' of
    (TArrow a b) -> do
      x' <- check env a x
      return $ App b f' x' 
    _ -> throwError "Expected arrow type"
synth env (Var _ x) = do
  t' <- lookupVar x env 
  return $ Var t' x
synth _ _ = throwError "Expected E-term"

holeType :: Scheme
holeType = Forall [TV "a"] $ tvar "a"