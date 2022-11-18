module RoundTrip (
    check
  , checkGoal
) where

import Language
import Checker

checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)
checkGoal env s e = do
  typ <- instantiate s
  check env typ e

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check env typ (Hole _ _) = throwError "Hole in term"
check env typ (Lam _ x e) = 
  case typ of
    (TArrow a b) -> check (extend x a env) b e
    _ -> throwError "Expected arrow type"
check env typ e = do
  t' <- strengthen env typ e
  return e

-- Infer type
strengthen :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
strengthen env typ (Hole _ _) = throwError "Hole in term"
strengthen env typ (App _ f x) = do
  f' <- strengthen env (tany --> typ) f 
  case annotation f' of
    (TArrow a b) -> do
      x' <- check env b x
      checkE typ b
      return $ App b f' x' 
    _ -> throwError "Expected arrow type"
strengthen env typ (Var _ x) = do
  t' <- lookupVar x env 
  checkE t' typ
  return $ Var t' x
strengthen env _ _ = throwError "Expected E-term"

checkE :: MonadND m => Type -> Type -> Checker m ()
checkE t t' = do
  addConstraint (t, t')
  solveAll