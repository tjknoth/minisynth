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

addConstraint :: Monad m => Constraint -> Checker m ()
addConstraint c = do
  st@(TypingState _ cs _) <- get
  put $ st { constraints = c:cs }

-- Check against goal type
check :: Monad m => Environment -> Type -> Term Type -> Checker m (Term Type)
check env typ (Lam _ x e) = 
  case typ of
    (TArrow a b) -> check (extend x a env) b e
    _ -> undefined -- error
check env typ e = do
  t' <- synth env e
  addConstraint (annotation t', typ)
  return e

-- Infer type
synth :: Monad m => Environment -> Term Type -> Checker m (Term Type)
synth env (App _ f x) = do
  f' <- synth env f 
  case annotation f' of
    (TArrow a b) -> do
      x' <- check env b x
      return $ App b f' x' 
    _ -> undefined -- error
synth env (Var _ x) = do
  t' <- lookupVar x env 
  return $ Var t' x
synth env _ = undefined -- error

lookupVar :: Monad m => Id -> Environment -> Checker m Type
lookupVar x (Env e) =
  case Map.lookup x e of
    Nothing -> undefined -- error
    Just s -> instantiate s -- instantiate

fresh :: Monad m  => Checker m Type
fresh = do
  st@(TypingState _ _ f) <- get
  put $ st { freshState = f + 1 }
  return $ tvar $ "A" ++ show f

instantiate :: Monad m => Scheme -> Checker m Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  return $ apply s t

solve :: Monad m => [Constraint] -> Checker m ()
solve cs = undefined