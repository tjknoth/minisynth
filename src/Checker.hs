module Checker (
    check
) where

import Language

import qualified Data.Map as Map
import           Control.Monad.State

type Constraint = (Type, Type) 

data TypingState = TypingState {
    assignment :: Subst
  , constraints :: [Constraint]
  , freshState :: Int
}

type Checker = StateT TypingState

type MonadND m = (Monad m, MonadPlus m)

throwError :: MonadND m => String -> Checker m a 
throwError msg = mzero

addConstraint :: MonadND m => Constraint -> Checker m ()
addConstraint c = do
  st@(TypingState _ cs _) <- get
  put $ st { constraints = c:cs }

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check env typ (Lam _ x e) = 
  case typ of
    (TArrow a b) -> check (extend x a env) b e
    _ -> throwError "Expected arrow type"
check env typ e = do
  t' <- synth env e
  addConstraint (annotation t', typ)
  return e

-- Infer type
synth :: MonadND m => Environment -> Term Type -> Checker m (Term Type)
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

lookupVar :: MonadND m => Id -> Environment -> Checker m Type
lookupVar x (Env e) =
  case Map.lookup x e of
    Nothing -> undefined -- error
    Just s -> instantiate s -- instantiate

fresh :: MonadND m  => Checker m Type
fresh = do
  st@(TypingState _ _ f) <- get
  put $ st { freshState = f + 1 }
  return $ tvar $ "A" ++ show f

instantiate :: MonadND m => Scheme -> Checker m Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  return $ apply s t

solve :: MonadND m => [Constraint] -> Checker m ()
solve cs = undefined

currentAssignment :: MonadND m => Type -> Checker m Type
currentAssignment t = do
  s <- gets assignment
  return $ apply s t