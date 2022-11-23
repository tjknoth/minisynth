[1mdiff --git a/src/Gradual.hs b/src/Gradual.hs[m
[1mindex 03603df..d75fec7 100644[m
[1m--- a/src/Gradual.hs[m
[1m+++ b/src/Gradual.hs[m
[36m@@ -13,33 +13,32 @@[m [mcheckGoal env s@(Forall _ typ) = check (bindGoal s env) typ[m
 check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)[m
 check _ _ (Hole _ (Filled e)) = return e[m
 check env typ (Hole _ _) =[m
[31m-  return $ Hole typ $ Spec env typ[m
[32m+[m[32m  return $ Hole typ $ Spec env typ [RLam, RSym, RApp][m
 check env (TArrow a b) e =[m
   case e of[m
     (Lam _ x body) -> Lam (a --> b) x <$> check (extend x a env) b body [m
[31m-    _ -> throwError "Expected lambda"[m
[31m-check env typ e = do[m
[31m-  t' <- synth env e[m
[31m-  addConstraint $ Constraint env (annotation t') typ[m
[32m+[m[32m    _ -> synth env (a --> b) e[m[41m [m
[32m+[m[32mcheck env typ e = synth env typ e[m
[32m+[m
[32m+[m[32mcheckE :: MonadND m => Environment -> Type -> Type -> Checker m ()[m
[32m+[m[32mcheckE env t t' = do[m
[32m+[m[32m  addConstraint $ Constraint env t t'[m
   solveAll[m
[31m-  return t' [m
 [m
 -- Infer type[m
[31m-synth :: MonadND m => Environment -> Term Type -> Checker m (Term Type)[m
[31m-synth _ (Hole _ (Filled e)) = return e[m
[31m-synth env (Hole _ _) = return $ Hole TAny $ Spec env TAny[m
[31m-synth env (App _ f x) = do[m
[31m-  f' <- synth env f [m
[32m+[m[32msynth :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)[m
[32m+[m[32msynth _ _ (Hole _ (Filled e)) = return e[m
[32m+[m[32msynth env typ (Hole _ _) = return $ Hole typ $ Spec env typ [RSym, RApp][m
[32m+[m[32msynth env typ (App _ f x) = do[m
[32m+[m[32m  f' <- synth env (tany --> typ) f[m
   case annotation f' of[m
[31m-    TAny -> return $ f' $$ x[m
     (TArrow a b) -> do[m
       x' <- check env a x[m
[31m-      return $ App b f' x' [m
[32m+[m[32m      checkE env typ b[m
[32m+[m[32m      return $ App b f' x'[m
     _ -> throwError "Expected arrow type"[m
[31m-synth env (Var _ x) = do[m
[31m-  t' <- lookupVar x env [m
[32m+[m[32msynth env typ (Var _ x) = do[m
[32m+[m[32m  t' <- lookupVar x env[m
[32m+[m[32m  checkE env t' typ[m
   return $ Var t' x[m
[31m-synth _ _ = throwError "Expected E-term"[m
[31m-[m
[31m---holeType :: Scheme[m
[31m---holeType = Forall [TV "a"] $ tvar "a"[m
\ No newline at end of file[m
[32m+[m[32msynth _ _ _ = throwError "Expected E-term"[m
\ No newline at end of file[m
[1mdiff --git a/src/Language.hs b/src/Language.hs[m
[1mindex ccb48e1..6253a7b 100644[m
[1m--- a/src/Language.hs[m
[1m+++ b/src/Language.hs[m
[36m@@ -7,6 +7,7 @@[m [mmodule Language ([m
   , Term (..)[m
   , Type (..)[m
   , TVar (..)[m
[32m+[m[32m  , Rule (..)[m
   , Environment (..)[m
   , Subst[m
   , Scheme (..)[m
[36m@@ -33,7 +34,10 @@[m [mimport           Data.List (intercalate)[m
 [m
 type Id = String[m
 [m
[31m-data Hole = NoSpec | Spec Environment Type | Filled (Term Type)[m
[32m+[m[32mdata Rule = RLam | RSym | RApp[m
[32m+[m[32m  deriving (Show, Eq, Ord)[m
[32m+[m
[32m+[m[32mdata Hole = NoSpec | Spec Environment Type [Rule] | Filled (Term Type)[m
   deriving (Eq, Ord, Show)[m
 [m
 -- (Potentially annotated) program term[m
[36m@@ -60,11 +64,11 @@[m [mlam = Lam TAny[m
 hole :: Term Type[m
 hole = Hole TAny NoSpec[m
 [m
[31m-spechole :: Environment -> Type -> Term Type[m
[31m-spechole e t = Hole TAny $ Spec e t[m
[32m+[m[32mspechole :: Environment -> Type -> [Rule] -> Term Type[m
[32m+[m[32mspechole e t rs = Hole TAny $ Spec e t rs[m
 [m
 filled :: Term Type -> Term Type[m
[31m-filled = Hole TAny . Filled[m
[32m+[m[32mfilled e = Hole (annotation e) $ Filled e[m
 [m
 -- Primitive types[m
 data Prim = Int | Bool [m
[1mdiff --git a/src/RoundTrip.hs b/src/RoundTrip.hs[m
[1mindex 76b0ed2..1d17d59 100644[m
[1m--- a/src/RoundTrip.hs[m
[1m+++ b/src/RoundTrip.hs[m
[36m@@ -1,10 +1,16 @@[m
 module RoundTrip ([m
     check[m
   , checkGoal[m
[32m+[m[32m  , synthesizeRoundTrip[m
[32m+[m[32m  , generateScheme[m
 ) where[m
 [m
 import Language[m
 import Checker[m
[32m+[m[32mimport Synthesizer (Synthesizer, SynthesizerState (..), synthesize)[m
[32m+[m
[32m+[m[32mimport qualified Data.Map as Map[m
[32m+[m[32mimport           Control.Monad.State[m
 [m
 checkGoal :: MonadND m => Environment -> Scheme -> Term Type -> Checker m (Term Type)[m
 checkGoal env s@(Forall _ typ) = check (bindGoal s env) typ[m
[36m@@ -12,10 +18,10 @@[m [mcheckGoal env s@(Forall _ typ) = check (bindGoal s env) typ[m
 -- Check against goal type[m
 check :: MonadND m => Environment -> Type -> Term Type -> Checker m (Term Type)[m
 check _ _ (Hole _ _) = throwError "Hole in term"[m
[31m-check env typ (Lam _ x e) = [m
[31m-  case typ of[m
[31m-    (TArrow a b) -> check (extend x a env) b e[m
[31m-    _ -> throwError "Expected arrow type"[m
[32m+[m[32mcheck env (TArrow a b) e =[m
[32m+[m[32m  case e of[m
[32m+[m[32m    (Lam _ x body) -> check (extend x a env) b body[m
[32m+[m[32m    _ -> throwError "Expected lambda"[m
 check env typ e = strengthen env typ e[m
 [m
 -- Infer type[m
[36m@@ -38,4 +44,47 @@[m [mstrengthen _ _ _ = throwError "Expected E-term"[m
 checkE :: MonadND m => Environment -> Type -> Type -> Checker m ()[m
 checkE env t t' = do[m
   addConstraint $ Constraint env t t'[m
[31m-  solveAll[m
\ No newline at end of file[m
[32m+[m[32m  solveAll[m
[32m+[m
[32m+[m
[32m+[m[32m-- Synthesizer stuff[m
[32m+[m
[32m+[m[32msynthesizeRoundTrip :: String -> Int -> Environment -> Scheme -> IO ()[m
[32m+[m[32msynthesizeRoundTrip = synthesize generateScheme[m
[32m+[m
[32m+[m[32mgenerateScheme :: MonadND m => Environment -> Scheme -> Synthesizer m (Term Type)[m
[32m+[m[32mgenerateScheme env s@(Forall _ t) = generateI (bindGoal s env) t[m
[32m+[m
[32m+[m[32mgenerateI :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)[m
[32m+[m[32mgenerateI env (TArrow a b) = do[m
[32m+[m[32m  x <- lift freshId[m
[32m+[m[32m  lam x <$> generateI (extend x a env) b[m
[32m+[m[32mgenerateI env typ = do[m
[32m+[m[32m  (SynthesizerState m) <- get[m
[32m+[m[32m  enumerateUpTo m env typ[m
[32m+[m
[32m+[m[32menumerateUpTo :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)[m
[32m+[m[32menumerateUpTo d e t = do[m
[32m+[m[32m  d' <- msum $ map return [1..d][m
[32m+[m[32m  enumerateAt d' e t[m
[32m+[m
[32m+[m[32menumerateAt :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)[m
[32m+[m[32menumerateAt d env typ[m
[32m+[m[32m  | d <= 1 = do[m
[32m+[m[32m      x <- var <$> msum (map return (Map.keys (vars env)))[m
[32m+[m[32m      lift $ strengthen env typ x[m
[32m+[m[32m  | otherwise = do[m
[32m+[m[32m      guard (arity typ < maxArity)[m
[32m+[m[32m      -- This is ugly but whatever[m
[32m+[m[32m      app <- enumerateApp (enumerateUpTo (d - 1)) (enumerateAt (d - 1)) `mplus` enumerateApp (enumerateAt d) (enumerateUpTo (d - 1))[m
[32m+[m[32m      lift $ checkE env typ (annotation app)[m
[32m+[m[32m      return app[m
[32m+[m[32m      where[m
[32m+[m[32m        maxArity = maximum $ map (arity . toMonotype) (Map.elems (vars env))[m
[32m+[m[32m        enumerateApp fun arg = do[m
[32m+[m[32m          f <- fun env (tany --> typ)[m
[32m+[m[32m          case annotation f of[m
[32m+[m[32m            (TArrow a b) -> do[m
[32m+[m[32m              x <- arg env a[m
[32m+[m[32m              return $ App b f x[m
[32m+[m[32m            _ -> error "Expected error type"[m
\ No newline at end of file[m
[1mdiff --git a/src/Synthesizer.hs b/src/Synthesizer.hs[m
[1mindex c16db5a..cebd12a 100644[m
[1m--- a/src/Synthesizer.hs[m
[1m+++ b/src/Synthesizer.hs[m
[36m@@ -1,5 +1,9 @@[m
 module Synthesizer ([m
[31m-    runSynthesizer[m
[32m+[m[32m    Synthesizer[m
[32m+[m[32m  , SynthesizerState (..)[m
[32m+[m[32m  , synthesizeGradual[m
[32m+[m[32m  , explore[m
[32m+[m[32m  , runSynthesizer[m
   , synthesize[m
   , solveGoal[m
 ) where[m
[36m@@ -8,6 +12,7 @@[m [mimport Language[m
 import Checker[m
 import Gradual[m
 [m
[32m+[m[32mimport           Control.Monad.Logic[m
 import qualified Data.Map as Map[m
 import           Control.Monad[m
 import           Control.Monad.State[m
[36m@@ -16,20 +21,28 @@[m [mnewtype SynthesizerState = SynthesizerState Int[m
 [m
 type Synthesizer m = StateT SynthesizerState (Checker m)[m
 [m
[31m-synthesize :: String -> Int -> Environment -> Scheme -> IO ()[m
[31m-synthesize name m env sch = do[m
[31m-  res <- solveGoal m env sch [m
[32m+[m
[32m+[m[32msynthesize :: (Environment -> Scheme -> Synthesizer (LogicT IO) (Term Type))[m[41m [m
[32m+[m[32m           -> String -> Int -> Environment -> Scheme -> IO ()[m
[32m+[m[32msynthesize go name m env sch = do[m
[32m+[m[32m  res <- solveGoal go m env sch[m
   case res of[m
     Nothing -> putStrLn "Impossible synthesis goal"[m
     Just t -> do[m
       putStrLn $ unwords [name, "::", pretty sch][m
       putStrLn $ pretty t[m
 [m
[31m-solveGoal :: Int -> Environment -> Scheme -> IO (Maybe (Term Type))[m
[31m-solveGoal m env sch = runChecker (runSynthesizer m env sch)[m
[32m+[m[32msolveGoal :: (Environment -> Scheme -> Synthesizer (LogicT IO) (Term Type))[m[41m [m
[32m+[m[32m          -> Int -> Environment -> Scheme -> IO (Maybe (Term Type))[m
[32m+[m[32msolveGoal go m env sch = runChecker (runSynthesizer go m env sch)[m
[32m+[m
[32m+[m[32mrunSynthesizer :: MonadND m[m[41m [m
[32m+[m[32m               => (Environment -> Scheme -> Synthesizer m (Term Type))[m
[32m+[m[32m               -> Int -> Environment -> Scheme -> Checker m (Term Type)[m
[32m+[m[32mrunSynthesizer go m env sch = evalStateT (go env sch) (SynthesizerState m)[m
 [m
[31m-runSynthesizer :: MonadND m => Int -> Environment -> Scheme -> Checker m (Term Type)[m
[31m-runSynthesizer m env sch = evalStateT (explore env sch) (SynthesizerState m)[m
[32m+[m[32msynthesizeGradual :: String -> Int -> Environment -> Scheme -> IO ()[m
[32m+[m[32msynthesizeGradual = synthesize explore[m
 [m
 explore :: MonadND m => Environment -> Scheme -> Synthesizer m (Term Type)[m
 explore env sch = do[m
[36m@@ -37,21 +50,22 @@[m [mexplore env sch = do[m
   (SynthesizerState m) <- get[m
   d <- msum $ map return [1..m][m
   case h' of[m
[31m-    (Hole _ (Spec env' typ)) -> generate d env' typ h' [m
[32m+[m[32m    (Hole _ (Spec env' typ _)) -> generate d env' typ h'[m[41m [m
     _ -> error "Expected annotated hole"[m
 [m
 generate :: MonadND m => Int -> Environment -> Type -> Term Type -> Synthesizer m (Term Type)[m
 generate _ _ _ (Hole _ NoSpec) = error "Expected annotated hole"[m
 generate _ _ _ (Hole _ (Filled t)) = return t[m
[31m-generate d _ _ (Hole _ (Spec env typ)) = fillAt d env typ[m
[32m+[m[32mgenerate d _ _ (Hole _ (Spec env typ rs)) = fillAt d env typ rs[m
 generate d env typ (Lam _ x e) = do[m
   l' <- lift $ check env typ (lam x e)[m
   case l' of[m
[31m-    (Lam _ _ (Hole _ (Spec env' typ'))) -> do[m
[31m-      body <- fillAt d env' typ'[m
[32m+[m[32m    (Lam _ _ (Hole _ (Spec env' typ' rs))) -> do[m
[32m+[m[32m      body <- fillAt d env' typ' rs[m
       lift $ check env typ $ lam x (filled body)[m
     _ -> error "Expected lambda"[m
 generate d env typ (App _ f x) = do[m
[32m+[m[32m  guard (not (null (vars env)))[m
   guard (arity typ < maxArity)[m
   -- This is ugly but whatever[m
   enumerateApp (fillUpTo (d - 1)) (fillAt (d - 1)) `mplus` enumerateApp (fillAt d) (fillUpTo (d - 1))[m
[36m@@ -60,25 +74,31 @@[m [mgenerate d env typ (App _ f x) = do[m
     enumerateApp fun arg = do[m
       f' <- lift $ check env typ (f $$ x) [m
       case f' of [m
[31m-        (App _ (Hole _ (Spec fEnv fTyp)) _) -> do[m
[31m-          fActual <- fun fEnv fTyp[m
[32m+[m[32m        (App _ (Hole _ (Spec fEnv fTyp frs)) _) -> do[m
[32m+[m[32m          fActual <- fun fEnv fTyp frs[m
           app' <- lift $ check env typ (filled fActual $$ x)[m
           case app' of[m
[31m-            (App _ _ (Hole _ (Spec xEnv xTyp))) -> do[m
[31m-              xActual <- arg xEnv xTyp[m
[32m+[m[32m            (App _ _ (Hole _ (Spec xEnv xTyp xrs))) -> do[m
[32m+[m[32m              xActual <- arg xEnv xTyp xrs[m
               lift $ check env typ (fActual $$ filled xActual)[m
             _ -> error "Argument not a hole"[m
         _ -> error $ "Function not a hole: " ++ show f'[m
 generate _ env typ e@Var{} = lift $ check env typ e[m
 [m
[31m-fillUpTo :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)[m
[31m-fillUpTo d env typ = do[m
[32m+[m[32mfillUpTo :: MonadND m => Int -> Environment -> Type -> [Rule] -> Synthesizer m (Term Type)[m
[32m+[m[32mfillUpTo d env typ rs = do[m
   d' <- msum $ map return [1..d][m
[31m-  fillAt d' env typ[m
[32m+[m[32m  fillAt d' env typ rs[m
[32m+[m
[32m+[m[32mfillAt :: MonadND m => Int -> Environment -> Type -> [Rule] -> Synthesizer m (Term Type)[m
[32m+[m[32mfillAt d env typ rs = msum (map return rs) >>= applyRule d env typ >>= generate d env typ[m
 [m
[31m-fillAt :: MonadND m => Int -> Environment -> Type -> Synthesizer m (Term Type)[m
[31m-fillAt d env typ = [m
[31m-  msum [generateLambda env typ, if d > 1 then generateApp env typ else generateSym env typ] >>= generate d env typ[m
[32m+[m[32mapplyRule :: MonadND m => Int -> Environment -> Type -> Rule -> Synthesizer m (Term Type)[m
[32m+[m[32mapplyRule d env typ r =[m
[32m+[m[32m  case r of[m
[32m+[m[32m    RLam -> generateLambda env typ[m
[32m+[m[32m    RSym -> if d <= 1 then generateSym env typ else mzero[m
[32m+[m[32m    RApp -> if d > 1 then generateApp env typ else mzero[m
 [m
 generateLambda :: MonadND m => Environment -> Type -> Synthesizer m (Term Type)[m
 generateLambda _ _ = do[m
