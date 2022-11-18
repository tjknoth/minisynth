module Gradual (
    check
  , checkGoal
) where

import Control.Monad.IO.Class

import Language
import Checker

checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)
checkGoal env s e = do
  typ <- instantiate s
  check env typ e

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check env typ (Hole _ _) =
  return $ Hole typ $ Just $ Spec typ env
check env typ (Lam _ x e) = 
  case typ of
    (TArrow a b) -> check (extend x a env) b e
    _ -> throwError "Expected arrow type"
check env typ e = do
  t' <- synth env e
  liftIO $ print $ "Synthed: " ++ show t'
  addConstraint (annotation t', typ)
  solveAll
  return e

-- Infer type
synth :: MonadND m => Environment -> Term Type -> Checker m (Term Type)
synth env (Hole _ _) = do
  t <- instantiate holeType 
  return $ Hole t $ Just $ Spec t env
synth env (App _ f x) = do
  f' <- synth env f 
  case annotation f' of
    (TArrow a b) -> do
      x' <- check env b x
      return $ App b f' x' 
    _ -> throwError "Expected arrow type"
synth env (Var _ x) = do
  t' <- lookupVar x env 
  return $ Var t' x
synth env _ = throwError "Expected E-term"

holeType :: Scheme
holeType = Forall [TV "a"] $ tvar "a"