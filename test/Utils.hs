{-# LANGUAGE RankNTypes #-}
module Utils where

import Data.Proxy
import Test.QuickCheck

import Data.DecisionDiagram.BDD.Internal.ItemOrder

forAllItemOrder :: Testable prop => (forall o. ItemOrder o => Proxy o -> prop) -> Property
forAllItemOrder k =
  forAllShow chooseAny (\x -> if x then "AscOrder" else "DescOrder") $ \b ->
    if b then withAscOrder k else withDescOrder k
