module Synthesizer (
    runSynthesizer
  , synthesize
) where

import Language
import Checker
import Gradual

import qualified Data.Map as Map
import           Control.Monad
import           Control.Monad.State

newtype SynthesizerState = SynthesizerState Int

type Synthesizer m = StateT SynthesizerState (Checker m)

synthesize :: Int -> Environment -> Scheme -> IO (Maybe (Term Type))
synthesize m env sch = runChecker (runSynthesizer m env sch)

runSynthesizer :: MonadND m => Int -> Environment -> Scheme -> Checker m (Term Type)
runSynthesizer m env sch = evalStateT (explore env sch) (SynthesizerState m)

explore :: MonadND m => Environment -> Scheme -> Synthesizer m (Term Type)
explore env sch = do
  h' <- lift $ checkGoal env sch hole
  (SynthesizerState m) <- get
  d <- msum $ map return [1..m]
  case h' of
    (Hole _ (Spec env' typ)) -> generate d env' typ h' 
    _ -> error "Expected annotated hole"

generate :: MonadND m => Int -> Environment -> Type -> Term Type -> Synthesizer m (Term Type)
generate _ _ _ (Hole _ NoSpec) = error "Expected annotated hole"
generate _ _ _ (Hole _ (Filled t)) = return t
generate d _ _ (Hole _ (Spec env typ)) = fillAt d env typ
generate d env typ (Lam _ x e) = do
  l' <- lift $ check env typ (lam x e)
  case l' of
    (Lam _ _ (Hole _ (Spec env' typ'))) -> do
      body <- fillAt d env' typ'
      lift $ check env typ $ lam x (filled body)
    _ -> error "Expected lambda"
generate d env typ (App _ f x) = do
  guard (arity typ < maxArity)
  enumerateApp (fillUpTo (d - 1)) (fillAt (d - 1)) `mplus` enumerateApp (fillAt d) (fillUpTo (d - 1))
  where
    maxArity = maximum $ map (arity . toMonotype) (Map.elems (vars env))
    enumerateApp fun arg = do
      f' <- lift $ check env typ (f $$ x) 
      case f' of 
        (App _ (Hole _ (Spec fEnv fTyp)) _) -> do
          fActual <- fun fEnv fTyp -- TODO: don't be dumb
          app' <- lift $ check env typ (filled fActual $$ x)
          case app' of
            (App _ _ (Hole _ (Spec xEnv xTyp))) -> do
              xActual <- arg xEnv xTyp -- TODO: don't be dumb
              lift $ check env typ (fActual $$ filled xActual)
            _ -> error "Argument not a hole"
        _ -> error "Function not a hole"
generate _ env typ e@Var{} = lift $ check env typ e

fillUpTo :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)
fillUpTo d env typ = do
  d' <- msum $ map return [1..d]
  fillAt d' env typ

fillAt :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)
fillAt d env typ = msum [generateLambda env typ, if d > 1 then generateApp env typ else generateSym env typ] >>= generate d env typ

generateLambda :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateLambda _ _ = do
  x <- lift freshId
  return $ lam x hole

generateApp :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateApp _ _ = return (hole $$ hole)

generateSym :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)
generateSym env _ = var <$> msum (map return (Map.keys (vars env)))