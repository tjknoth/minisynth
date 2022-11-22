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
  return $ Hole typ $ Spec env typ
check env (TArrow a b) e =
  case e of
    (Lam _ x body) -> Lam (a --> b) x <$> check (extend x a env) b body 
    _ -> throwError "Expected lambda"
check env typ e = do
  t' <- synth env e
  addConstraint $ Constraint env (annotation t') typ
  solveAll
  return t' 

-- Infer type
synth :: MonadND m => Environment -> Term Type -> Checker m (Term Type)
synth _ (Hole _ (Filled e)) = return e
synth env (Hole _ _) = return $ Hole TAny $ Spec env TAny
synth env (App _ f x) = do
  f' <- synth env f 
  case annotation f' of
    TAny -> return $ f' $$ x
    (TArrow a b) -> do
      x' <- check env a x
      return $ App b f' x' 
    _ -> throwError "Expected arrow type"
synth env (Var _ x) = do
  t' <- lookupVar x env 
  return $ Var t' x
synth _ _ = throwError "Expected E-term"

--holeType :: Scheme
--holeType = Forall [TV "a"] $ tvar "a"