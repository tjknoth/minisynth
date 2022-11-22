{-# LANGUAGE ConstraintKinds #-}

module Checker (
    MonadND
  , Checker
  , Constraint (..)
  , runChecker
  , typecheck
  , throwError
  , addConstraint
  , lookupVar
  , solveAll
  , instantiate
  , instantiateGoal
  , freshId
) where

import Language

import qualified Data.Set as Set
import qualified Data.Map as Map
import           Control.Monad.State
import           Control.Monad.Logic


data Constraint = Constraint Environment Type Type
  deriving (Eq, Ord, Show)

instance Substitutable Constraint where
  apply s (Constraint e t t') = Constraint e (apply s t) (apply s t')
  ftv (Constraint _ t t') = ftv t `Set.union` ftv t'

data TypingState = TypingState {
    assignment :: Subst
  , constraints :: [Constraint]
  , freshTVars :: Int
  , freshVars :: Int
}

initTS :: TypingState
initTS = TypingState nullSubst [] 0 0

type Checker = StateT TypingState

runChecker :: Checker (LogicT IO) a -> IO (Maybe a)
runChecker go = do
  r <- observeManyT 1 (evalStateT go initTS) 
  case r of
    []    -> return Nothing
    (a:_) -> return $ Just a

typecheck :: (Environment -> Scheme -> Term Type -> Checker (LogicT IO) (Term Type))
          -> Environment
          -> Scheme 
          -> Term Type
          -> IO (Maybe (Term Type))
typecheck check env typ term = runChecker (check env typ term)

type MonadND m = (Monad m, MonadPlus m, MonadIO m)

throwError :: MonadND m => String -> Checker m a 
throwError _ = do 
  -- liftIO $ putStrLn msg -- hacky
  mzero

addConstraint :: MonadND m => Constraint -> Checker m ()
addConstraint c = do
  st@(TypingState _ cs _ _) <- get
  put $ st { constraints = c:cs }

lookupVar :: MonadND m => Id -> Environment -> Checker m Type
lookupVar x (Env e _) =
  case Map.lookup x e of
    Nothing -> throwError "variable not found" -- error
    Just s -> instantiate s -- instantiate

fresh :: MonadND m  => Checker m Type
fresh = do
  st@(TypingState _ _ f _) <- get
  put $ st { freshTVars = f + 1 }
  return $ tvar $ "A" ++ show f

freshId :: MonadND m  => Checker m Id
freshId = do
  st@(TypingState _ _ _ f) <- get
  put $ st { freshVars = f + 1 }
  return $ "X" ++ show f

instantiate :: MonadND m => Scheme -> Checker m Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  return $ apply s t

instantiateGoal :: Scheme -> Environment -> Environment
instantiateGoal (Forall as _) (Env vs tvs) = Env vs $ foldr Set.insert tvs as

isBound :: TVar -> Environment -> Bool
isBound tv (Env _ tvs) = tv `Set.member` tvs

solveAll :: MonadND m => Checker m ()
solveAll = do
  s' <- solve
  st <- get
  put $ st { assignment = s' }

solve :: MonadND m => Checker m Subst
solve = do 
  st@(TypingState su cs _ _) <- get
  case cs of
    [] -> return su
    (Constraint env t1 t2: cs0) -> do
      (su1, cs1) <- unifies env t1 t2
      put $ st { assignment = su1 `compose` su, constraints = cs1 ++ apply su1 cs0 }
      solve 

type Unifier = (Subst, [Constraint])

emptyUnifer :: Unifier
emptyUnifer = (nullSubst, [])

unifies :: MonadND m => Environment -> Type -> Type -> Checker m Unifier
unifies _ TAny _ = return emptyUnifer
unifies _ _ TAny = return emptyUnifer
unifies _ t1 t2 | t1 == t2 = return emptyUnifer
unifies env (TVar v) t | not (isBound v env) = v `bind` t
unifies env t (TVar v) | not (isBound v env) = v `bind` t
unifies env (TArrow t1 t2) (TArrow t3 t4) = unifyMany env [t1, t2] [t3, t4]
unifies _ _ _ = throwError "unification fail"

unifyMany :: MonadND m => Environment -> [Type] -> [Type] -> Checker m Unifier
unifyMany _ [] [] = return emptyUnifer
unifyMany env (t1 : ts1) (t2 : ts2) =
  do (su1,cs1) <- unifies env t1 t2
     (su2,cs2) <- unifyMany env (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1, cs1 ++ cs2)
unifyMany _ _ _ = throwError "unification mismatch"

bind :: MonadND m => TVar -> Type -> Checker m Unifier 
bind a t | t == TVar a = return (nullSubst, [])
         | occurs a t  = throwError "infinite type" 
         | otherwise   = return (Map.singleton a t, [])