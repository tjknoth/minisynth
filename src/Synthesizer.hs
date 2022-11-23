module Synthesizer (
    Synthesizer
  , SynthesizerState (..)
  , synthesizeGradual
  , explore
  , runSynthesizer
  , synthesize
  , solveGoal
) where

import Language
import Checker
import Gradual

import           Control.Monad.Logic
import qualified Data.Map as Map
import           Control.Monad
import           Control.Monad.State

newtype SynthesizerState = SynthesizerState Int

type Synthesizer m = StateT SynthesizerState (Checker m)


synthesize :: (Environment -> Scheme -> Synthesizer (LogicT IO) (Term Type)) 
           -> String -> Int -> Environment -> Scheme -> IO ()
synthesize go name m env sch = do
  res <- solveGoal go m env sch
  case res of
    Nothing -> putStrLn "Impossible synthesis goal"
    Just t -> do
      putStrLn $ unwords [name, "::", pretty sch]
      putStrLn $ pretty t

solveGoal :: (Environment -> Scheme -> Synthesizer (LogicT IO) (Term Type)) 
          -> Int -> Environment -> Scheme -> IO (Maybe (Term Type))
solveGoal go m env sch = runChecker (runSynthesizer go m env sch)

runSynthesizer :: MonadND m 
               => (Environment -> Scheme -> Synthesizer m (Term Type))
               -> Int -> Environment -> Scheme -> Checker m (Term Type)
runSynthesizer go m env sch = evalStateT (go env sch) (SynthesizerState m)

synthesizeGradual :: String -> Int -> Environment -> Scheme -> IO ()
synthesizeGradual = synthesize explore

explore :: MonadND m => Environment -> Scheme -> Synthesizer m (Term Type)
explore env sch = do
  h' <- lift $ checkGoal env sch hole
  (SynthesizerState m) <- get
  d <- msum $ map return [1..m]
  case h' of
    (Hole _ (Spec env' typ _)) -> generate d env' typ h' 
    _ -> error "Expected annotated hole"

generate :: MonadND m => Int -> Environment -> Type -> Term Type -> Synthesizer m (Term Type)
generate _ _ _ (Hole _ NoSpec) = error "Expected annotated hole"
generate _ _ _ (Hole _ (Filled t)) = return t
generate d _ _ (Hole _ (Spec env typ rs)) = fillAt d env typ rs
generate d env typ (Lam _ x e) = do
  l' <- lift $ check env typ (lam x e)
  case l' of
    (Lam _ _ (Hole _ (Spec env' typ' rs))) -> do
      body <- fillAt d env' typ' rs
      lift $ check env typ $ lam x (filled body)
    _ -> error "Expected lambda"
generate d env typ (App _ f x) = do
  guard (not (null (vars env)))
  guard (arity typ < maxArity)
  -- This is ugly but whatever
  enumerateApp (fillUpTo (d - 1)) (fillAt (d - 1)) `mplus` enumerateApp (fillAt d) (fillUpTo (d - 1))
  where
    maxArity = maximum $ map (arity . toMonotype) (Map.elems (vars env))
    enumerateApp fun arg = do
      f' <- lift $ check env typ (f $$ x) 
      case f' of 
        (App _ (Hole _ (Spec fEnv fTyp frs)) _) -> do
          fActual <- fun fEnv fTyp frs
          app' <- lift $ check env typ (filled fActual $$ x)
          case app' of
            (App _ _ (Hole _ (Spec xEnv xTyp xrs))) -> do
              xActual <- arg xEnv xTyp xrs
              lift $ check env typ (fActual $$ filled xActual)
            _ -> error "Argument not a hole"
        _ -> error $ "Function not a hole: " ++ show f'
generate _ env typ e@Var{} = lift $ check env typ e

fillUpTo :: MonadND m => Int -> Environment -> Type -> [Rule] -> Synthesizer m (Term Type)
fillUpTo d env typ rs = do
  d' <- msum $ map return [1..d]
  fillAt d' env typ rs

fillAt :: MonadND m => Int -> Environment -> Type -> [Rule] -> Synthesizer m (Term Type)
fillAt d env typ rs = msum (map return rs) >>= applyRule d env typ >>= generate d env typ

applyRule :: MonadND m => Int -> Environment -> Type -> Rule -> Synthesizer m (Term Type)
applyRule d env typ r =
  case r of
    RLam -> generateLambda env typ
    RSym -> if d <= 1 then generateSym env typ else mzero
    RApp -> if d > 1 then generateApp env typ else mzero

generateLambda :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateLambda _ _ = do
  x <- lift freshId
  return $ lam x hole

generateApp :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateApp _ _ = return (hole $$ hole)

generateSym :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateSym env _ = var <$> msum (map return (Map.keys (vars env)))