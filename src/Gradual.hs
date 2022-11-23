module Gradual (
    check
  , checkGoal
) where

import Language
import Checker

checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)
checkGoal env s@(Forall _ typ) = check (bindGoal s env) typ

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check _ _ (Hole _ (Filled e)) = return e
check env typ (Hole _ _) =
  return $ Hole typ $ Spec env typ [RLam, RSym, RApp]
check env (TArrow a b) e =
  case e of
    (Lam _ x body) -> Lam (a --> b) x <$> check (extend x (monotype a) env) b body 
    _ -> synth env (a --> b) e
check env typ e = synth env typ e

checkE :: MonadND m => Environment -> Type -> Type -> Checker m ()
checkE env t t' = do
  addConstraint $ Constraint env t t'
  solveAll

-- Infer type
synth :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
synth _ _ (Hole _ (Filled e)) = return e
synth env typ (Hole _ _) = return $ Hole typ $ Spec env typ [RSym, RApp]
synth env typ (App _ f x) = do
  f' <- synth env (tany --> typ) f
  case annotation f' of
    (TArrow a b) -> do
      x' <- check env a x
      checkE env typ b
      return $ App b f' x'
    _ -> throwError "Expected arrow type"
synth env typ (Var _ x) = do
  t' <- lookupVar x env
  checkE env typ t'
  return $ Var t' x
synth _ _ _ = throwError "Expected E-term"