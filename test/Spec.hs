import           Language
import           Checker
import qualified RoundTrip as RT
import qualified Gradual as G

main :: IO ()
main = do
  print ""
  gradualTests
  print ""
  roundTripTests

data Result = Error | OK

check go (OK, t, e) = do
  r <- runChecker go initEnv t e
  if r
    then print "OK"
    else print $ "Error on OK term: " ++ show e
check go (Error, t, e) = do
  r <- runChecker go initEnv t e
  if r
    then print $ "Checked bad term: " ++ show e
    else print "OK" 

gradualTests :: IO ()
gradualTests = do
  print "Gradual typechecker:"
  mapM_ (check G.checkGoal) tests

roundTripTests :: IO ()
roundTripTests = do
  print "Round trip typechecker:"
  mapM_ (check RT.checkGoal) tests

tests :: [(Result, Scheme, Term Type)]
tests = [
    (OK, Forall [TV "a"] (tvar "a" --> tvar "a"), lam "x" (var "x")) -- \x.x :: a -> a
  , (Error, Forall [TV "a", TV "b"] (tvar "a" --> tvar "b"), lam "x" (var "x")) -- \x.x :: a -> b
  ]