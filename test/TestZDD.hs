{-# OPTIONS_GHC -Wall -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module TestZDD (zddTestGroup) where

import Control.Monad
import qualified Data.IntSet as IntSet
import Data.List
import Data.Proxy
import qualified Data.Set as Set
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.DecisionDiagram.BDD.Internal as Internal
import Data.DecisionDiagram.ZDD (ZDD (..))
import qualified Data.DecisionDiagram.ZDD as ZDD

-- ------------------------------------------------------------------------

instance ZDD.ItemOrder a => Arbitrary (ZDD a) where
  arbitrary = liftM ZDD $ do
    vars <- liftM (sortBy (ZDD.compareItem (Proxy :: Proxy a)) . IntSet.toList . IntSet.fromList) arbitrary
    let f vs n = oneof $
          [ return Internal.F
          , return Internal.T
          ]
          ++
          [ do v <- elements vs
               let vs' = dropWhile (\v' -> compareItem (Proxy :: Proxy a) v' v  /= GT) vs
               p0 <- f vs' (n `div` 2)
               p1 <- f vs' (n `div` 2) `suchThat` (/= Internal.F)
               return (Internal.Branch v p0 p1)
          | n > 0, not (null vs)
          ]
    sized (f vars)

  shrink (ZDD Internal.F) = []
  shrink (ZDD Internal.T) = []
  shrink (ZDD (Internal.Branch x p0 p1)) =
    [ZDD p0, ZDD p1]
    ++
    [ ZDD (Internal.Branch x p0' p1')
    | (ZDD p0', ZDD p1') <- shrink (ZDD p0 :: ZDD a, ZDD p1 :: ZDD a), p1' /= Internal.F
    ]

-- ------------------------------------------------------------------------
-- Union
-- ------------------------------------------------------------------------

prop_union_unitL :: Property
prop_union_unitL =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.empty `ZDD.union` a === a

prop_union_unitR :: Property
prop_union_unitR =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.union` ZDD.empty === a

prop_union_comm :: Property
prop_union_comm =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      a `ZDD.union` b === b `ZDD.union` a

prop_union_assoc :: Property
prop_union_assoc =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.union` (b `ZDD.union` c) === (a `ZDD.union` b) `ZDD.union` c

prop_union_idempotent :: Property
prop_union_idempotent =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.union` a === a

-- ------------------------------------------------------------------------
-- Intersection
-- ------------------------------------------------------------------------

prop_intersection_comm :: Property
prop_intersection_comm =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      a `ZDD.intersection` b === b `ZDD.intersection` a

prop_intersection_assoc :: Property
prop_intersection_assoc =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.intersection` (b `ZDD.intersection` c) === (a `ZDD.intersection` b) `ZDD.intersection` c

prop_intersection_idempotent :: Property
prop_intersection_idempotent =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.intersection` a === a

prop_intersection_emptyL :: Property
prop_intersection_emptyL =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.empty `ZDD.intersection` a === ZDD.empty

prop_intersection_emptyR :: Property
prop_intersection_emptyR =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.intersection` ZDD.empty === ZDD.empty

prop_intersection_distL :: Property
prop_intersection_distL =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.intersection` (b `ZDD.union` c) === (a `ZDD.intersection` b) `ZDD.union` (a `ZDD.intersection` c)

prop_intersection_distR :: Property
prop_intersection_distR =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      (a `ZDD.union` b) `ZDD.intersection` c === (a `ZDD.intersection` c) `ZDD.union` (b `ZDD.intersection` c)

-- ------------------------------------------------------------------------
-- Difference
-- ------------------------------------------------------------------------

prop_difference_cancel :: Property
prop_difference_cancel =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a ZDD.\\ a === ZDD.empty

prop_difference_unit :: Property
prop_difference_unit =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a ZDD.\\ ZDD.empty === a

prop_union_difference :: Property
prop_union_difference =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      (a `ZDD.union` b) ZDD.\\ c === (a ZDD.\\ c) `ZDD.union` (b ZDD.\\ c)

prop_difference_union :: Property
prop_difference_union =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a ZDD.\\ (b `ZDD.union` c) === (a ZDD.\\ b) ZDD.\\ c

-- ------------------------------------------------------------------------
-- Misc
-- ------------------------------------------------------------------------

prop_empty :: Property
prop_empty =
  withDefaultOrder $ \(_ :: Proxy o) ->
    ZDD.toSetOfIntSets (ZDD.empty :: ZDD o) === Set.empty

prop_unit :: Property
prop_unit =
  withDefaultOrder $ \(_ :: Proxy o) ->
    ZDD.toSetOfIntSets (ZDD.unit :: ZDD o) === Set.singleton IntSet.empty

prop_change :: Property
prop_change =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      let f xs
            | IntSet.member x xs = IntSet.delete x xs
            | otherwise = IntSet.insert x xs
       in ZDD.toSetOfIntSets (ZDD.change x a) === Set.map f (ZDD.toSetOfIntSets a)

prop_subset1 :: Property
prop_subset1 =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      ZDD.toSetOfIntSets (ZDD.subset1 x a) === Set.map (IntSet.delete x) (Set.filter (IntSet.member x) (ZDD.toSetOfIntSets a))

prop_subset0 :: Property
prop_subset0 =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      ZDD.toSetOfIntSets (ZDD.subset0 x a) === Set.filter (IntSet.notMember x) (ZDD.toSetOfIntSets a)

prop_size :: Property
prop_size =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.size a === Set.size (ZDD.toSetOfIntSets a)

-- ------------------------------------------------------------------------

zddTestGroup :: TestTree
zddTestGroup = $(testGroupGenerator)
