module RoundTrip (
    check
  , checkGoal
  , synthesizeRoundTrip
  , generateScheme
) where

import Language
import Checker
import Synthesizer (Synthesizer, SynthesizerState (..), synthesize)

import qualified Data.Map as Map
import           Control.Monad.State

checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)
checkGoal env s@(Forall _ typ) = check (bindGoal s env) typ

-- Check against goal type
check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)
check _ _ (Hole _ _) = throwError "Hole in term"
check env (TArrow a b) e =
  case e of
    (Lam _ x body) -> check (extend x (monotype a) env) b body
    _ -> throwError "Expected lambda"
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


-- Synthesizer stuff

synthesizeRoundTrip :: String -> Int -> Environment -> Scheme -> IO ()
synthesizeRoundTrip = synthesize generateScheme

generateScheme :: MonadND m => Environment -> Scheme -> Synthesizer m (Term Type)
generateScheme env s@(Forall _ t) = generateI (bindGoal s env) t

generateI :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateI env (TArrow a b) = do
  x <- lift freshId
  lam x <$> generateI (extend x (monotype a) env) b
generateI env typ = do
  (SynthesizerState m) <- get
  enumerateUpTo m env typ

enumerateUpTo :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)
enumerateUpTo d e t = do
  d' <- msum $ map return [1..d]
  enumerateAt d' e t

enumerateAt :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)
enumerateAt d env typ
  | d <= 1 = do
      x <- var <$> msum (map return (Map.keys (vars env)))
      lift $ strengthen env typ x
  | otherwise = do
      guard (arity typ < maxArity)
      -- This is ugly but whatever
      app <- enumerateApp (enumerateUpTo (d - 1)) (enumerateAt (d - 1)) `mplus` enumerateApp (enumerateAt d) (enumerateUpTo (d - 1))
      lift $ checkE env typ (annotation app)
      return app
      where
        maxArity = maximum $ map (arity . toMonotype) (Map.elems (vars env))
        enumerateApp fun arg = do
          f <- fun env (tany --> typ)
          case annotation f of
            (TArrow a b) -> do
              x <- arg env a
              return $ App b f x
            _ -> error "Expected error type"