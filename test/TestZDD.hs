{-# OPTIONS_GHC -Wall -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module TestZDD (zddTestGroup) where

import Control.Monad
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import qualified GHC.Exts as Exts
import Statistics.Distribution
import Statistics.Distribution.ChiSquared (chiSquared)
import qualified System.Random.MWC as Rand
import qualified Test.QuickCheck.Monadic as QM
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.DecisionDiagram.ZDD (ZDD (..), ItemOrder (..), withDefaultOrder)
import qualified Data.DecisionDiagram.ZDD as ZDD

-- ------------------------------------------------------------------------

instance ZDD.ItemOrder a => Arbitrary (ZDD a) where
  arbitrary = do
    vars <- liftM (sortBy (ZDD.compareItem (Proxy :: Proxy a)) . IntSet.toList . IntSet.fromList) arbitrary
    let f vs n = oneof $
          [ return ZDD.empty
          , return ZDD.base
          ]
          ++
          [ do v <- elements vs
               let vs' = dropWhile (\v' -> compareItem (Proxy :: Proxy a) v' v  /= GT) vs
               p0 <- f vs' (n `div` 2)
               p1 <- f vs' (n `div` 2) `suchThat` (/= ZDD.empty)
               return (ZDD.Branch v p0 p1)
          | n > 0, not (null vs)
          ]
    sized (f vars)

  shrink (ZDD.Empty) = []
  shrink (ZDD.Base) = []
  shrink (ZDD.Branch x p0 p1) =
    [p0, p1]
    ++
    [ ZDD.Branch x p0' p1'
    | (p0', p1') <- shrink (p0, p1), p1' /= ZDD.empty
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
-- Non-superset
-- ------------------------------------------------------------------------

prop_nonSuperset :: Property
prop_nonSuperset =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      let a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
          p xs = and [not (IntSet.isSubsetOf ys xs) | ys <- Set.toList b']
       in ZDD.toSetOfIntSets (a `ZDD.nonSuperset` b) === Set.filter p a'

prop_nonSuperset_cancel :: Property
prop_nonSuperset_cancel =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.nonSuperset` a === ZDD.empty

prop_nonSuperset_unit :: Property
prop_nonSuperset_unit =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.nonSuperset` ZDD.empty === a

prop_union_nonSuperset :: Property
prop_union_nonSuperset =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      (a `ZDD.union` b) `ZDD.nonSuperset` c === (a `ZDD.nonSuperset` c) `ZDD.union` (b `ZDD.nonSuperset` c)

prop_nonSuperset_union :: Property
prop_nonSuperset_union =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.nonSuperset` (b `ZDD.union` c) === (a `ZDD.nonSuperset` b) `ZDD.nonSuperset` c

prop_nonSuperset_difference :: Property
prop_nonSuperset_difference =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      let c = a `ZDD.nonSuperset` b
          d = a ZDD.\\ b
       in counterexample (show (c, d)) $ c `ZDD.isSubsetOf` d

-- ------------------------------------------------------------------------
-- Minimal hitting sets
-- ------------------------------------------------------------------------

isHittingSetOf :: IntSet -> Set IntSet -> Bool
isHittingSetOf s g = all (\e -> not (IntSet.null (s `IntSet.intersection` e))) g

prop_minimalHittingSetsKnuth_isHittingSet :: Property
prop_minimalHittingSetsKnuth_isHittingSet =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsKnuth a
          a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
       in all (`isHittingSetOf` a') b'

prop_minimalHittingSetsImai_isHittingSet :: Property
prop_minimalHittingSetsImai_isHittingSet =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsImai a
          a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
       in all (`isHittingSetOf` a') b'

prop_minimalHittingSetsToda_isHittingSet :: Property
prop_minimalHittingSetsToda_isHittingSet =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsToda a
          a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
       in all (`isHittingSetOf` a') b'

prop_minimalHittingSetsKnuth_duality :: Property
prop_minimalHittingSetsKnuth_duality =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsKnuth a
       in ZDD.minimalHittingSetsKnuth (ZDD.minimalHittingSetsKnuth b) === b

prop_minimalHittingSetsImai_duality :: Property
prop_minimalHittingSetsImai_duality =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsImai a
       in ZDD.minimalHittingSetsImai (ZDD.minimalHittingSetsImai b) === b

prop_minimalHittingSetsToda_duality :: Property
prop_minimalHittingSetsToda_duality =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsToda a
       in ZDD.minimalHittingSetsToda (ZDD.minimalHittingSetsToda b) === b

prop_minimalHittingSets_Imai_equal_Knuth :: Property
prop_minimalHittingSets_Imai_equal_Knuth =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.minimalHittingSetsImai a === ZDD.minimalHittingSetsKnuth a

prop_minimalHittingSets_Toda_equal_Knuth :: Property
prop_minimalHittingSets_Toda_equal_Knuth =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.minimalHittingSetsToda a === ZDD.minimalHittingSetsKnuth a

-- ------------------------------------------------------------------------
-- Misc
-- ------------------------------------------------------------------------

prop_empty :: Property
prop_empty =
  withDefaultOrder $ \(_ :: Proxy o) ->
    ZDD.toSetOfIntSets (ZDD.empty :: ZDD o) === Set.empty

prop_base :: Property
prop_base =
  withDefaultOrder $ \(_ :: Proxy o) ->
    ZDD.toSetOfIntSets (ZDD.base :: ZDD o) === Set.singleton IntSet.empty

prop_singleton :: Property
prop_singleton =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll (liftM IntSet.fromList arbitrary) $ \xs ->
      let a :: ZDD o
          a = ZDD.singleton xs
       in counterexample (show a) $ ZDD.toSetOfIntSets a === Set.singleton xs

prop_toList_fromList :: Property
prop_toList_fromList =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xss ->
      let a :: ZDD o
          a = Exts.fromList xss
          f = Set.fromList
       in counterexample (show a) $ f (Exts.toList a) === f xss

prop_fromList_toList :: Property
prop_fromList_toList =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let xss = Exts.toList a
       in counterexample (show xss) $ Exts.fromList xss === a

prop_toSetOfIntSets_fromSetOfIntSets :: Property
prop_toSetOfIntSets_fromSetOfIntSets =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll (liftM (Set.fromList . map IntSet.fromList) arbitrary) $ \xss ->
      let a :: ZDD o
          a = ZDD.fromSetOfIntSets xss
       in counterexample (show a) $ ZDD.toSetOfIntSets a === xss

prop_fromSetOfIntSets_toSetOfIntSets :: Property
prop_fromSetOfIntSets_toSetOfIntSets =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let xss = ZDD.toSetOfIntSets a
       in counterexample (show xss) $ ZDD.fromSetOfIntSets xss === a

prop_insert :: Property
prop_insert =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (liftM IntSet.fromList arbitrary) $ \xs ->
        ZDD.toSetOfIntSets (ZDD.insert xs a) === Set.insert xs (ZDD.toSetOfIntSets a)

prop_insert_idempotent :: Property
prop_insert_idempotent =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (liftM IntSet.fromList arbitrary) $ \xs ->
        let b = ZDD.insert xs a
         in counterexample (show b) $ ZDD.insert xs b === b

prop_delete :: Property
prop_delete =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (liftM IntSet.fromList $ sublistOf (IntSet.toList (ZDD.flatten a))) $ \xs ->
        ZDD.toSetOfIntSets (ZDD.delete xs a) === Set.delete xs (ZDD.toSetOfIntSets a)

prop_delete_idempotent :: Property
prop_delete_idempotent =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (liftM IntSet.fromList $ sublistOf (IntSet.toList (ZDD.flatten a))) $ \xs ->
        let b = ZDD.delete xs a
         in counterexample (show b) $ ZDD.delete xs b === b

prop_mapInsert :: Property
prop_mapInsert =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        ZDD.toSetOfIntSets (ZDD.mapInsert x a) === Set.map (IntSet.insert x) (ZDD.toSetOfIntSets a)

prop_mapInsert_idempotent :: Property
prop_mapInsert_idempotent =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        let b = ZDD.mapInsert x a
         in counterexample (show b) $ ZDD.mapInsert x b === b

prop_mapDelete :: Property
prop_mapDelete =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        ZDD.toSetOfIntSets (ZDD.mapDelete x a) === Set.map (IntSet.delete x) (ZDD.toSetOfIntSets a)

prop_mapDelete_idempotent :: Property
prop_mapDelete_idempotent =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        let b = ZDD.mapDelete x a
         in counterexample (show b) $ ZDD.mapDelete x b === b

prop_change :: Property
prop_change =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      let f xs
            | IntSet.member x xs = IntSet.delete x xs
            | otherwise = IntSet.insert x xs
       in ZDD.toSetOfIntSets (ZDD.change x a) === Set.map f (ZDD.toSetOfIntSets a)

prop_change_involution :: Property
prop_change_involution =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        ZDD.change x (ZDD.change x a) === a

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

prop_member_1 :: Property
prop_member_1 =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      conjoin [counterexample (show xs) (ZDD.member xs a) | xs <- ZDD.toListOfIntSets a]

prop_member_2 :: Property
prop_member_2 =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (liftM IntSet.fromList $ sublistOf (IntSet.toList (ZDD.flatten a))) $ \s2 ->
        (s2 `ZDD.member` a) === (s2 `Set.member` ZDD.toSetOfIntSets a)

prop_size :: Property
prop_size =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.size a === Set.size (ZDD.toSetOfIntSets a)

prop_null_size :: Property
prop_null_size =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.null a === (ZDD.size a == (0 :: Int))

prop_isSubsetOf_refl :: Property
prop_isSubsetOf_refl =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.isSubsetOf` a

prop_isSubsetOf_empty :: Property
prop_isSubsetOf_empty =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.empty `ZDD.isSubsetOf` a

prop_isSubsetOf_and_isProperSubsetOf :: Property
prop_isSubsetOf_and_isProperSubsetOf =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      (a `ZDD.isSubsetOf` b) === (a `ZDD.isProperSubsetOf` b || a == b)

prop_isProperSubsetOf_not_refl :: Property
prop_isProperSubsetOf_not_refl =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      not (ZDD.isProperSubsetOf a a)

prop_disjoint :: Property
prop_disjoint =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      ZDD.disjoint a b === ZDD.null (a `ZDD.intersection` b)

prop_flatten :: Property
prop_flatten =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.flatten a === IntSet.unions (ZDD.toListOfIntSets a)

prop_uniformM :: Property
prop_uniformM =
  withDefaultOrder $ \(_ :: Proxy o) ->
    forAll (arbitrary `suchThat` ((>= (2::Integer)) . ZDD.size)) $ \(a :: ZDD o) ->
      QM.monadicIO $ do
        gen <- QM.run Rand.create
        let m :: Integer
            m = ZDD.size a
            n = 1000
        samples <- QM.run $ replicateM n $ ZDD.uniformM a gen
        let hist_actual = Map.fromListWith (+) [(s, 1) | s <- samples]
            hist_expected = [(s, fromIntegral n / fromIntegral m) | s <- ZDD.toListOfIntSets a]
            chi_sq = sum [(Map.findWithDefault 0 s hist_actual - cnt) ** 2 / cnt | (s, cnt) <- hist_expected]
            threshold = complQuantile (chiSquared (fromIntegral m - 1)) 0.001
        QM.monitor $ counterexample $ show hist_actual ++ " /= " ++ show (Map.fromList hist_expected)
        QM.assert $ and [xs `ZDD.member` a | xs <- Map.keys hist_actual]
        QM.monitor $ counterexample $ "χ² = " ++ show chi_sq ++ " >= " ++ show threshold
        QM.assert $ chi_sq < threshold

-- ------------------------------------------------------------------------

zddTestGroup :: TestTree
zddTestGroup = $(testGroupGenerator)
