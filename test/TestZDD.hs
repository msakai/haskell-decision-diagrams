{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TemplateHaskell #-}
module TestZDD (zddTestGroup) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

zddTestGroup :: TestTree
zddTestGroup = $(testGroupGenerator)
