module Main where

import Test.Tasty (defaultMain, testGroup)

import TestBDD
import TestZDD

main :: IO ()
main = defaultMain $ testGroup "decision-diagram test suite"
  [ bddTestGroup
  , zddTestGroup
  ]
