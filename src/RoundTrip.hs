module RoundTrip (
    check
  , checkGoal
) where

import Language
import Checker

checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)
checkGoal env s@(Forall _ typ) = check (instantiateGoal s env) typ

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check _ _ (Hole _ _) = throwError "Hole in term"
check env typ (Lam _ x e) = 
  case typ of
    (TArrow a b) -> check (extend x a env) b e
    _ -> throwError "Expected arrow type"
check env typ e = strengthen env typ e

-- Infer type
strengthen :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
strengthen _ _ (Hole _ _) = throwError "Hole in term"
strengthen env typ (App _ f x) = do
  f' <- strengthen env (tany --> typ) f 
  case annotation f' of
    (TArrow a b) -> do
      x' <- check env a x
      checkE env typ b
      return $ App b f' x' 
    _ -> throwError "Expected arrow type"
strengthen env typ (Var _ x) = do
  t' <- lookupVar x env 
  checkE env t' typ
  return $ Var t' x
strengthen _ _ _ = throwError "Expected E-term"

checkE :: MonadND m => Environment -> Type -> Type -> Checker m ()
checkE env t t' = do
  addConstraint $ Constraint env t t'
  solveAll