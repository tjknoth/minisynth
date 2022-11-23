{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Language
import RoundTrip (generateScheme)
import Synthesizer (explore, synthesize)
import System.Environment
import Data.Char (toLower)

-- Usage: minisynth [style]
-- where "style" is either "direct" or "indirect"
main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> error "Expected argument"
    (a:_) | map toLower a == "direct" -> benchmark True
          | map toLower a == "indirect" -> benchmark False
          | otherwise -> error "Invalid argument"


benchmark :: Bool -> IO ()
benchmark direct = 
  let go = if direct then generateScheme else explore
      name = "compose"
      depth = 10
      schema = Forall ["a", "b", "c"] (("a" --> "b") --> ("b" --> "c") --> "a" --> "c")
   in synthesize go name depth initEnv schema