{-# LANGUAGE ConstraintKinds #-}

module Checker (
    MonadND
  , Checker
  , runChecker
  , throwError
  , addConstraint
  , lookupVar
  , solveAll
  , instantiate
) where

import Language

import qualified Data.Map as Map
import           Control.Monad.State
import           Control.Monad.Logic


type Constraint = (Type, Type) 

data TypingState = TypingState {
    assignment :: Subst
  , constraints :: [Constraint]
  , freshState :: Int
}

initTS :: TypingState
initTS = TypingState nullSubst [] 0

type Checker = StateT TypingState

runChecker :: (Environment -> Scheme -> Term Type -> Checker (LogicT IO) (Term Type))
           -> Environment
           -> Scheme 
           -> Term Type
           -> IO Bool
runChecker check env typ term = do
  res <- observeManyT 1 (evalStateT (check env typ term ) initTS)
  return $ case res of
    [] -> False
    _:_ -> True

type MonadND m = (Monad m, MonadPlus m, MonadIO m)

throwError :: MonadND m => String -> Checker m a 
throwError _ = mzero

addConstraint :: MonadND m => Constraint -> Checker m ()
addConstraint c = do
  st@(TypingState _ cs _) <- get
  put $ st { constraints = c:cs }

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

solveAll :: MonadND m => Checker m ()
solveAll = do
  (TypingState su cs f) <- get
  liftIO $ print $ "Solving: " ++ show cs
  liftIO $ print $ "Assignment: " ++ show (Map.toList su)
  s' <- solve
  st <- get
  put $ st { assignment = s' }

solve :: MonadND m => Checker m Subst
solve = do 
  (TypingState su cs f) <- get
  case cs of
    [] -> return su
    ((t1, t2): cs0) -> do
      (su1, cs1)  <- unifies t1 t2
      put $ TypingState (su1 `compose` su) (cs1 ++ apply su1 cs0) f
      solve 

type Unifier = (Subst, [Constraint])

emptyUnifer :: Unifier
emptyUnifer = (nullSubst, [])

unifies :: MonadND m => Type -> Type -> Checker m Unifier
unifies t1 t2 | t1 == t2 = return emptyUnifer
unifies (TVar v) t = v `bind` t
unifies t (TVar v) = v `bind` t
unifies (TArrow t1 t2) (TArrow t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies _ _ = throwError "unification fail"

unifyMany :: MonadND m => [Type] -> [Type] -> Checker m Unifier
unifyMany [] [] = return emptyUnifer
unifyMany (t1 : ts1) (t2 : ts2) =
  do (su1,cs1) <- unifies t1 t2
     (su2,cs2) <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return (su2 `compose` su1, cs1 ++ cs2)
unifyMany _ _ = throwError "unification mismatch"

bind :: MonadND m => TVar -> Type -> Checker m Unifier 
bind a t | t == TVar a = return (nullSubst, [])
         | occurs a t  = throwError "infinite type" 
         | otherwise   = return $ (Map.singleton a t, [])

currentAssignment :: MonadND m => Type -> Checker m Type
currentAssignment t = do
  s <- gets assignment
  return $ apply s t