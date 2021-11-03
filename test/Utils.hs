{-# LANGUAGE RankNTypes #-}
module Utils
  ( forAllItemOrder
  ) where

import Data.Proxy
import Test.QuickCheck

import Data.DecisionDiagram.BDD.Internal.ItemOrder

data SomeItemOrder
  = AscOrder
  | DescOrder
  deriving (Show, Enum, Bounded)

instance Arbitrary SomeItemOrder where
  arbitrary = arbitraryBoundedEnum

forAllItemOrder :: Testable prop => (forall o. ItemOrder o => Proxy o -> prop) -> Property
forAllItemOrder k =
  forAll arbitrary $ \o ->
    case o of
      AscOrder -> withAscOrder k
      DescOrder -> withDescOrder k
