{-# LANGUAGE OverloadedStrings #-}

import           Language
import           Checker
import qualified RoundTrip as RT
import qualified Gradual as G
import           Synthesizer

import           Data.Maybe (isJust)
import           Control.Monad.Logic (LogicT)

main :: IO ()
main = do
  putStrLn ""
  gradualTests
  putStrLn ""
  roundTripTests
  putStrLn ""
  gradualSynthesisTests
  putStrLn ""
  roundTripSynthesisTests

data Result = Error | OK

check :: (Environment -> Scheme -> Term Type -> Checker (LogicT IO) (Term Type)) -> Result -> (Environment, Scheme, Term Type) -> IO ()
check go OK (env, typ, t) = do
  r <- isJust <$> typecheck go env typ t
  if r
    then putStrLn "OK"
    else putStrLn $ "Error on OK term: " ++ show t
check go Error (env, typ, t) = do
  r <- isJust <$> typecheck go env typ t
  if r
    then putStrLn $ "Checked bad term: " ++ show t
    else putStrLn "OK" 

gradualTests :: IO ()
gradualTests = do
  putStrLn "Gradual typechecker:"
  mapM_ (check G.checkGoal OK) posCheckingTests
  mapM_ (check G.checkGoal Error) negCheckingTests

roundTripTests :: IO ()
roundTripTests = do
  putStrLn "Round trip typechecker:"
  mapM_ (check RT.checkGoal OK) posCheckingTests
  mapM_ (check RT.checkGoal Error) negCheckingTests
 
gradualSynthesisTests :: IO ()
gradualSynthesisTests = do
  putStrLn "Gradual synthesizer:"
  mapM_ (synth explore) synthTests

roundTripSynthesisTests :: IO ()
roundTripSynthesisTests = do
  putStrLn "Round-Trip synthesizer:"
  mapM_ (synth RT.generateScheme) synthTests

synth :: (Environment -> Scheme -> Synthesizer (LogicT IO) (Term Type)) -> (Environment, Scheme) -> IO ()
synth go (env, sch) = do
  res <- solveGoal go 5 env sch -- TODO: don't bake-in depth
  case res of
    Nothing -> putStrLn "Synthesis failed"
    Just t -> do
      ok <- isJust <$> typecheck G.checkGoal env sch (TAny <$ t)
      if ok
        then putStrLn "OK"
      else putStrLn "Synthesized bad term"



posCheckingTests :: [(Environment, Scheme, Term Type)]
posCheckingTests = [
    (initEnv, Forall ["a"] ("a" --> "a"), lam "x" "x")
  , (initEnv, Forall ["a", "a"] (("a" --> "b") --> "a" --> "b"), lam "f" (lam "x" ("f" $$ "x")))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "b") --> ("b" --> "c") --> "a" --> "c"), lam "f" (lam "g" (lam "x" ("g" $$ ("f" $$ "x")))))
  , (initEnv, Forall [] (tbool --> tbool), lam "x" "x")
  , (initEnv, Forall [] (tint --> tint), lam "x" "x")
  , (initEnv, Forall [] ((tint --> tbool) --> tint --> tbool), lam "f" (lam "x" ("f" $$ "x")))
  , (initEnv, Forall ["a"] ((tint --> "a") --> tint --> "a"), lam "f" (lam "x" ("f" $$ "x")))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "b" --> "c") --> "a" --> "b" --> "c"), lam "f" (lam "x" (lam "y" ("f" $$ "x" $$ "y"))))
  , (initEnv, Forall ["a", "b", "c", "d"] (("a" --> "b") --> ("b" --> "c") --> ("c" --> "d") --> "a" --> "d"), lam "f" (lam "g" (lam "h" (lam "x" ("h" $$ ("g" $$ ("f" $$ "x")))))))
  ]

-- Negative tests: should fail
negCheckingTests :: [(Environment, Scheme, Term Type)]
negCheckingTests = [
    (initEnv, Forall ["a", "b"] ("a" --> "b"), lam "x" "x")
  , (initEnv, Forall ["a", "a"] (("a" --> "b") --> "a" --> "b"), lam "f" (lam "x" ("x" $$ "f")))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "b") --> ("b" --> "c") --> "a" --> "c"), lam "f" (lam "g" (lam "x" ("f" $$ ("g" $$ "x")))))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "a") --> ("b" --> "c") --> "a" --> "c"), lam "f" (lam "g" (lam "x" ("g" $$ ("f" $$ "x")))))
  , (initEnv, Forall ["a"] (tint --> "a"), lam "x" "x")
  , (initEnv, Forall ["a"] (tint --> "a"), lam "x" "y")
  , (initEnv, Forall ["a", "b"] ((tint --> "a") --> "b" --> "a"), lam "f" (lam "x" ("f" $$ "x")))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "b" --> "c") --> "a" --> "b" --> "c"), lam "f" (lam "x" (lam "y" ("f" $$ "x" $$ "x"))))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "b" --> "c") --> "a" --> "b" --> "c"), lam "f" (lam "x" (lam "y" ("f" $$ "x" $$ "x"))))
  , (idEnv, Forall ["a", "b", "c"] (("a" --> "b" --> "c") --> "a" --> "b" --> "c"), lam "f" (lam "x" (lam "y" ("id" $$ "f"))))
  , (idEnv, Forall ["a", "b", "c"] (("a" --> "b" --> "c") --> "a" --> "b" --> "c"), lam "f" (lam "x" (lam "y" ("f" $$ "id" $$ "y"))))
  , (idEnv, Forall ["a", "b", "c", "d"] (("a" --> "b") --> ("b" --> "c") --> ("c" --> "d") --> "a" --> "d"), lam "f" (lam "g" (lam "h" (lam "x" ("h" $$ ("id" $$ ("f" $$ "x")))))))
  ]

synthTests :: [(Environment, Scheme)]
synthTests = [
    (initEnv, Forall ["a"] ("a" --> "a"))
  , (initEnv, Forall ["a", "b"] (("a" --> "b") --> "a" --> "b"))
  , (initEnv, Forall ["a", "b", "c"] (("a" --> "b") --> ("b" --> "c") --> "a" --> "c"))
  , (initEnv, Forall ["a", "b", "c", "d"] (("a" --> "b") --> ("b" --> "c") --> ("c" --> "d") --> "a" --> "d"))
  , (idEnv, Forall ["a", "b"] (("a" --> "b") --> "a" --> "b"))
  , (idEnv, Forall ["a", "b", "c"] (("a" --> "b") --> ("b" --> "c") --> "a" --> "c"))
  , (idEnv, Forall ["a", "b", "c", "d"] (("a" --> "b") --> ("b" --> "c") --> ("c" --> "d") --> "a" --> "d"))
  ]

idEnv :: Environment
idEnv = extend "id" (Forall ["a"] ("a" --> "a")) initEnv