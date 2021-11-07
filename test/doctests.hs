module Main (main) where

import Test.DocTest

main :: IO ()
main = doctest
  [ "-isrc"
  , "src/Data/DecisionDiagram/BDD.hs"
  , "src/Data/DecisionDiagram/ZDD.hs"
  ]
