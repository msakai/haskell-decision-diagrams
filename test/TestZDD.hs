{-# OPTIONS_GHC -Wall -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module TestZDD (zddTestGroup) where

import Control.DeepSeq
import Control.Monad
import Control.Monad.ST
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import Data.List
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import Data.Word
import qualified GHC.Exts as Exts
import Statistics.Distribution
import Statistics.Distribution.ChiSquared (chiSquared)
import System.IO.Unsafe
import qualified System.Random.MWC as Rand
import Test.QuickCheck.Function (apply)
import Test.QuickCheck.Instances.Vector ()
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.DecisionDiagram.BDD.Internal.ItemOrder (OrderedItem (..))
import Data.DecisionDiagram.ZDD (ZDD (..), ItemOrder (..))
import qualified Data.DecisionDiagram.ZDD as ZDD

import Utils

-- ------------------------------------------------------------------------

instance ZDD.ItemOrder a => Arbitrary (ZDD a) where
  arbitrary = do
    vars <- liftM (sortBy (ZDD.compareItem (Proxy :: Proxy a)) . IntSet.toList) arbitrary
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

arbitraryMember :: ZDD.ItemOrder a => ZDD a -> Gen IntSet
arbitraryMember zdd = do
  (seed :: Vector Word32) <- arbitrary
  return $ runST $ do
    gen <- Rand.initialize seed
    ZDD.uniformM zdd gen

-- ------------------------------------------------------------------------
-- Union
-- ------------------------------------------------------------------------

prop_union_unitL :: Property
prop_union_unitL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.empty `ZDD.union` a === a

prop_union_unitR :: Property
prop_union_unitR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.union` ZDD.empty === a

prop_union_comm :: Property
prop_union_comm =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      a `ZDD.union` b === b `ZDD.union` a

prop_union_assoc :: Property
prop_union_assoc =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.union` (b `ZDD.union` c) === (a `ZDD.union` b) `ZDD.union` c

prop_union_idempotent :: Property
prop_union_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.union` a === a

-- ------------------------------------------------------------------------
-- Intersection
-- ------------------------------------------------------------------------

prop_intersection_comm :: Property
prop_intersection_comm =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      a `ZDD.intersection` b === b `ZDD.intersection` a

prop_intersection_assoc :: Property
prop_intersection_assoc =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.intersection` (b `ZDD.intersection` c) === (a `ZDD.intersection` b) `ZDD.intersection` c

prop_intersection_idempotent :: Property
prop_intersection_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.intersection` a === a

prop_intersection_emptyL :: Property
prop_intersection_emptyL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.empty `ZDD.intersection` a === ZDD.empty

prop_intersection_emptyR :: Property
prop_intersection_emptyR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.intersection` ZDD.empty === ZDD.empty

prop_intersection_distL :: Property
prop_intersection_distL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.intersection` (b `ZDD.union` c) === (a `ZDD.intersection` b) `ZDD.union` (a `ZDD.intersection` c)

prop_intersection_distR :: Property
prop_intersection_distR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      (a `ZDD.union` b) `ZDD.intersection` c === (a `ZDD.intersection` c) `ZDD.union` (b `ZDD.intersection` c)

-- ------------------------------------------------------------------------
-- Difference
-- ------------------------------------------------------------------------

prop_difference_cancel :: Property
prop_difference_cancel =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a ZDD.\\ a === ZDD.empty

prop_difference_unit :: Property
prop_difference_unit =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a ZDD.\\ ZDD.empty === a

prop_union_difference :: Property
prop_union_difference =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      (a `ZDD.union` b) ZDD.\\ c === (a ZDD.\\ c) `ZDD.union` (b ZDD.\\ c)

prop_difference_union :: Property
prop_difference_union =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a ZDD.\\ (b `ZDD.union` c) === (a ZDD.\\ b) ZDD.\\ c

-- ------------------------------------------------------------------------
-- Non-superset
-- ------------------------------------------------------------------------

prop_nonSuperset :: Property
prop_nonSuperset =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      let a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
          p xs = and [not (IntSet.isSubsetOf ys xs) | ys <- Set.toList b']
       in ZDD.toSetOfIntSets (a `ZDD.nonSuperset` b) === Set.filter p a'

prop_nonSuperset_cancel :: Property
prop_nonSuperset_cancel =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.nonSuperset` a === ZDD.empty

prop_nonSuperset_unit :: Property
prop_nonSuperset_unit =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.nonSuperset` ZDD.empty === a

prop_union_nonSuperset :: Property
prop_union_nonSuperset =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      (a `ZDD.union` b) `ZDD.nonSuperset` c === (a `ZDD.nonSuperset` c) `ZDD.union` (b `ZDD.nonSuperset` c)

prop_nonSuperset_union :: Property
prop_nonSuperset_union =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b, c) ->
      a `ZDD.nonSuperset` (b `ZDD.union` c) === (a `ZDD.nonSuperset` b) `ZDD.nonSuperset` c

prop_nonSuperset_difference :: Property
prop_nonSuperset_difference =
  forAllItemOrder $ \(_ :: Proxy o) ->
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
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsKnuth a
          a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
       in all (`isHittingSetOf` a') b'

prop_minimalHittingSetsImai_isHittingSet :: Property
prop_minimalHittingSetsImai_isHittingSet =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsImai a
          a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
       in all (`isHittingSetOf` a') b'

prop_minimalHittingSetsToda_isHittingSet :: Property
prop_minimalHittingSetsToda_isHittingSet =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsToda a
          a' = ZDD.toSetOfIntSets a
          b' = ZDD.toSetOfIntSets b
       in all (`isHittingSetOf` a') b'

prop_minimalHittingSetsKnuth_duality :: Property
prop_minimalHittingSetsKnuth_duality =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsKnuth a
       in ZDD.minimalHittingSetsKnuth (ZDD.minimalHittingSetsKnuth b) === b

prop_minimalHittingSetsImai_duality :: Property
prop_minimalHittingSetsImai_duality =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsImai a
       in ZDD.minimalHittingSetsImai (ZDD.minimalHittingSetsImai b) === b

prop_minimalHittingSetsToda_duality :: Property
prop_minimalHittingSetsToda_duality =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let b = ZDD.minimalHittingSetsToda a
       in ZDD.minimalHittingSetsToda (ZDD.minimalHittingSetsToda b) === b

prop_minimalHittingSets_Imai_equal_Knuth :: Property
prop_minimalHittingSets_Imai_equal_Knuth =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.minimalHittingSetsImai a === ZDD.minimalHittingSetsKnuth a

prop_minimalHittingSets_Toda_equal_Knuth :: Property
prop_minimalHittingSets_Toda_equal_Knuth =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.minimalHittingSetsToda a === ZDD.minimalHittingSetsKnuth a

-- ------------------------------------------------------------------------
-- Misc
-- ------------------------------------------------------------------------

prop_empty :: Property
prop_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    ZDD.toSetOfIntSets (ZDD.empty :: ZDD o) === Set.empty

prop_base :: Property
prop_base =
  forAllItemOrder $ \(_ :: Proxy o) ->
    ZDD.toSetOfIntSets (ZDD.base :: ZDD o) === Set.singleton IntSet.empty

prop_singleton :: Property
prop_singleton =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      let a :: ZDD o
          a = ZDD.singleton xs
       in counterexample (show a) $ ZDD.toSetOfIntSets a === Set.singleton xs

prop_subsets_member :: Property
prop_subsets_member =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      let a :: ZDD o
          a = ZDD.subsets xs
       in counterexample (show a) $ forAll (subsetOf xs) $ \ys ->
            ys `ZDD.member` a

prop_subsets_member_empty :: Property
prop_subsets_member_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      let a :: ZDD o
          a = ZDD.subsets xs
       in counterexample (show a) $ IntSet.empty `ZDD.member` a

prop_subsets_member_itself :: Property
prop_subsets_member_itself =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      let a :: ZDD o
          a = ZDD.subsets xs
       in counterexample (show a) $ xs `ZDD.member` a

prop_subsets_size :: Property
prop_subsets_size =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      let a :: ZDD o
          a = ZDD.subsets xs
       in counterexample (show a) $ ZDD.size a === (2 :: Integer) ^ (IntSet.size xs)

prop_subsetsAtLeast :: Property
prop_subsetsAtLeast =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        let a :: ZDD o
            a = ZDD.subsetsAtLeast xs k
         in counterexample (show a) $
              if ZDD.null a then
                property (k > sum [max 0 w | (_,w) <- IntMap.toList xs])
              else
                forAll (arbitraryMember a) $ \ys ->
                  (ys `IntSet.isSubsetOf` IntMap.keysSet xs)
                  .&&.
                  sum [xs IntMap.! y | y <- IntSet.toList ys] >= k

prop_subsetsAtMost :: Property
prop_subsetsAtMost =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        let a :: ZDD o
            a = ZDD.subsetsAtMost xs k
         in counterexample (show a) $
              if ZDD.null a then
                property (k < sum [min 0 w | (_,w) <- IntMap.toList xs])
              else
                forAll (arbitraryMember a) $ \ys ->
                  (ys `IntSet.isSubsetOf` IntMap.keysSet xs)
                  .&&.
                  sum [xs IntMap.! y | y <- IntSet.toList ys] <= k

prop_subsetsExactly :: Property
prop_subsetsExactly =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        let a :: ZDD o
            a = ZDD.subsetsExactly xs k
         in counterexample (show a) $
              if ZDD.null a then
                property True
              else
                forAll (arbitraryMember a) $ \ys ->
                  (ys `IntSet.isSubsetOf` IntMap.keysSet xs)
                  .&&.
                  sum [xs IntMap.! y | y <- IntSet.toList ys] === k

prop_subsetsExactly_2 :: Property
prop_subsetsExactly_2 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll (gen xs) $ \(ys, k) ->
        let a :: ZDD o
            a = ZDD.subsetsExactly xs k
         in counterexample (show a) $ ys `ZDD.member` a
  where
    gen xs = do
      ys <- sublistOf (IntMap.toList xs)
      return (IntSet.fromList [y | (y,_) <- ys], sum [w | (_,w) <- ys])

prop_subsetsExactlyIntegral :: Property
prop_subsetsExactlyIntegral =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        (ZDD.subsetsExactlyIntegral xs k :: ZDD o) === ZDD.subsetsExactly xs k

prop_combinations_are_combinations :: Property
prop_combinations_are_combinations =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      forAll arbitrary $ \(NonNegative k) ->
        let a :: ZDD o
            a = ZDD.combinations xs k
         in counterexample (show a) $
              not (ZDD.null a)
              ==>
              (forAll (arbitraryMember a) $ \ys -> (ys `IntSet.isSubsetOf` xs) .&&. (IntSet.size ys === k))

prop_combinations_size :: Property
prop_combinations_size =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      forAll arbitrary $ \(NonNegative k) ->
        let a :: ZDD o
            a = ZDD.combinations xs k
            n = toInteger $ IntSet.size xs
         in counterexample (show a) $ ZDD.size a === (product [(n - toInteger k + 1)..n] `div` (product [1..toInteger k]))

case_toList_lazyness :: Assertion
case_toList_lazyness = do
  let xss :: ZDD ZDD.AscOrder
      xss = ZDD.subsets (IntSet.fromList [1..128])
  deepseq (take 100 (Exts.toList xss)) $ return ()

prop_toList_sorted :: Property
prop_toList_sorted =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(xss :: ZDD o) ->
      let yss :: [[OrderedItem o]]
          yss = map (sort . map OrderedItem . IntSet.toList) $ take 100 $ Exts.toList xss
       in yss ===  sort yss

prop_toList_fromList :: Property
prop_toList_fromList =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xss ->
      let a :: ZDD o
          a = Exts.fromList xss
          f = Set.fromList
       in counterexample (show a) $ f (Exts.toList a) === f xss

prop_fromList_toList :: Property
prop_fromList_toList =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let xss = Exts.toList a
       in counterexample (show xss) $ Exts.fromList xss === a

prop_toSetOfIntSets_fromSetOfIntSets :: Property
prop_toSetOfIntSets_fromSetOfIntSets =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xss ->
      let a :: ZDD o
          a = ZDD.fromSetOfIntSets xss
       in counterexample (show a) $ ZDD.toSetOfIntSets a === xss

prop_fromSetOfIntSets_toSetOfIntSets :: Property
prop_fromSetOfIntSets_toSetOfIntSets =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      let xss = ZDD.toSetOfIntSets a
       in counterexample (show xss) $ ZDD.fromSetOfIntSets xss === a

prop_insert :: Property
prop_insert =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \xs ->
        ZDD.toSetOfIntSets (ZDD.insert xs a) === Set.insert xs (ZDD.toSetOfIntSets a)

prop_insert_idempotent :: Property
prop_insert_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \xs ->
        let b = ZDD.insert xs a
         in counterexample (show b) $ ZDD.insert xs b === b

prop_delete :: Property
prop_delete =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (subsetOf (ZDD.flatten a)) $ \xs ->
        ZDD.toSetOfIntSets (ZDD.delete xs a) === Set.delete xs (ZDD.toSetOfIntSets a)

prop_delete_idempotent :: Property
prop_delete_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (subsetOf (ZDD.flatten a)) $ \xs ->
        let b = ZDD.delete xs a
         in counterexample (show b) $ ZDD.delete xs b === b

prop_mapInsert :: Property
prop_mapInsert =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        ZDD.toSetOfIntSets (ZDD.mapInsert x a) === Set.map (IntSet.insert x) (ZDD.toSetOfIntSets a)

prop_mapInsert_idempotent :: Property
prop_mapInsert_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        let b = ZDD.mapInsert x a
         in counterexample (show b) $ ZDD.mapInsert x b === b

prop_mapDelete :: Property
prop_mapDelete =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        ZDD.toSetOfIntSets (ZDD.mapDelete x a) === Set.map (IntSet.delete x) (ZDD.toSetOfIntSets a)

prop_mapDelete_idempotent :: Property
prop_mapDelete_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        let b = ZDD.mapDelete x a
         in counterexample (show b) $ ZDD.mapDelete x b === b

prop_change :: Property
prop_change =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      let f xs
            | IntSet.member x xs = IntSet.delete x xs
            | otherwise = IntSet.insert x xs
       in ZDD.toSetOfIntSets (ZDD.change x a) === Set.map f (ZDD.toSetOfIntSets a)

prop_change_involution :: Property
prop_change_involution =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll arbitrary $ \x ->
        ZDD.change x (ZDD.change x a) === a

prop_subset1 :: Property
prop_subset1 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      ZDD.toSetOfIntSets (ZDD.subset1 x a) === Set.map (IntSet.delete x) (Set.filter (IntSet.member x) (ZDD.toSetOfIntSets a))

prop_subset0 :: Property
prop_subset0 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
    forAll arbitrary $ \x ->
      ZDD.toSetOfIntSets (ZDD.subset0 x a) === Set.filter (IntSet.notMember x) (ZDD.toSetOfIntSets a)

prop_member_1 :: Property
prop_member_1 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      conjoin [counterexample (show xs) (ZDD.member xs a) | xs <- ZDD.toListOfIntSets a]

prop_member_2 :: Property
prop_member_2 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      forAll (subsetOf (ZDD.flatten a)) $ \s2 ->
        (s2 `ZDD.member` a) === (s2 `Set.member` ZDD.toSetOfIntSets a)

prop_size :: Property
prop_size =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.size a === Set.size (ZDD.toSetOfIntSets a)

prop_null_size :: Property
prop_null_size =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.null a === (ZDD.size a == (0 :: Int))

prop_isSubsetOf_refl :: Property
prop_isSubsetOf_refl =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      a `ZDD.isSubsetOf` a

prop_isSubsetOf_empty :: Property
prop_isSubsetOf_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.empty `ZDD.isSubsetOf` a

prop_isSubsetOf_and_isProperSubsetOf :: Property
prop_isSubsetOf_and_isProperSubsetOf =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      (a `ZDD.isSubsetOf` b) === (a `ZDD.isProperSubsetOf` b || a == b)

prop_isProperSubsetOf_not_refl :: Property
prop_isProperSubsetOf_not_refl =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      not (ZDD.isProperSubsetOf a a)

prop_disjoint :: Property
prop_disjoint =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o, b) ->
      ZDD.disjoint a b === ZDD.null (a `ZDD.intersection` b)

case_numNodes :: Assertion
case_numNodes = do
  let bdd, bdd1 :: ZDD ZDD.AscOrder
      bdd = ZDD.Branch 0 (ZDD.Branch 1 ZDD.empty bdd1) (ZDD.Branch 2 ZDD.empty bdd1)
      bdd1 = ZDD.Branch 3 ZDD.empty ZDD.base
  ZDD.numNodes bdd @?= 6

prop_flatten :: Property
prop_flatten =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.flatten a === IntSet.unions (ZDD.toListOfIntSets a)

prop_uniformM :: Property
prop_uniformM =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll (arbitrary `suchThat` ((>= (2::Integer)) . ZDD.size)) $ \(a :: ZDD o) ->
      forAll arbitrary $ \(seed :: Vector Word32) ->
        let m :: Integer
            m = ZDD.size a
            n = 1000
            samples = runST $ do
              gen <- Rand.initialize seed
              replicateM n $ ZDD.uniformM a gen
            hist_actual = Map.fromListWith (+) [(s, 1) | s <- samples]
            hist_expected = [(s, fromIntegral n / fromIntegral m) | s <- ZDD.toListOfIntSets a]
            chi_sq = sum [(Map.findWithDefault 0 s hist_actual - cnt) ** 2 / cnt | (s, cnt) <- hist_expected]
            threshold = complQuantile (chiSquared (fromIntegral m - 1)) 0.0001
         in counterexample (show hist_actual ++ " /= " ++ show (Map.fromList hist_expected)) $
              and [xs `ZDD.member` a | xs <- Map.keys hist_actual] .&&.
              counterexample ("χ² = " ++ show chi_sq ++ " >= " ++ show threshold) (chi_sq < threshold)

prop_findMinSum :: Property
prop_findMinSum =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll (arbitrary `suchThat` (not . ZDD.null)) $ \(a :: ZDD o) ->
      forAll arbitrary $ \(weight' :: Fun Int Integer) ->
        let weight = apply weight'
            setWeight s = sum [weight x | x <- IntSet.toList s]
            (obj0, s0) = ZDD.findMinSum weight a
         in counterexample (show [(x, weight x) | x <- IntSet.toList (ZDD.flatten a)]) $
            counterexample (show (obj0, s0)) $
              setWeight s0 === obj0
              .&&.
              conjoin [counterexample (show (s, setWeight s)) $ obj0 <= setWeight s | s <- ZDD.toListOfIntSets a]

prop_findMaxSum :: Property
prop_findMaxSum =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll (arbitrary `suchThat` (not . ZDD.null)) $ \(a :: ZDD o) ->
      forAll arbitrary $ \(weight' :: Fun Int Integer) ->
        let weight = apply weight'
            setWeight s = sum [weight x | x <- IntSet.toList s]
            (obj0, s0) = ZDD.findMaxSum weight a
         in counterexample (show [(x, weight x) | x <- IntSet.toList (ZDD.flatten a)]) $
            counterexample (show (obj0, s0)) $
              setWeight s0 === obj0
              .&&.
              conjoin [counterexample (show (s, setWeight s)) $ obj0 >= setWeight s | s <- ZDD.toListOfIntSets a]

-- ------------------------------------------------------------------------

case_fold_laziness :: Assertion
case_fold_laziness = do
  let bdd :: ZDD ZDD.AscOrder
      bdd = ZDD.Branch 0 (ZDD.Branch 1 ZDD.Empty ZDD.Base) (ZDD.Branch 2 ZDD.Empty ZDD.Base)
      f x lo _hi =
        if x == 2 then
          error "unused value should not be evaluated"
        else
          lo
  seq (ZDD.fold False True f bdd) $ return ()

case_fold'_strictness :: Assertion
case_fold'_strictness = do
  ref <- newIORef False
  let bdd :: ZDD ZDD.AscOrder
      bdd = ZDD.Branch 0 (ZDD.Branch 1 ZDD.Empty ZDD.Base) (ZDD.Branch 2 ZDD.Empty ZDD.Base)
      f x lo _hi = unsafePerformIO $ do
        when (x==2) $ writeIORef ref True
        return lo
  seq (ZDD.fold' False True f bdd) $ do
    flag <- readIORef ref
    assertBool "unused value should be evaluated" flag

prop_fold_inSig :: Property
prop_fold_inSig =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(zdd :: ZDD o) ->
      ZDD.fold (ZDD.inSig ZDD.SEmpty) (ZDD.inSig ZDD.SBase) (\x lo hi -> ZDD.inSig (ZDD.SBranch x lo hi)) zdd
      ===
      zdd

prop_fold'_inSig :: Property
prop_fold'_inSig =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(zdd :: ZDD o) ->
      ZDD.fold' (ZDD.inSig ZDD.SEmpty) (ZDD.inSig ZDD.SBase) (\x lo hi -> ZDD.inSig (ZDD.SBranch x lo hi)) zdd
      ===
      zdd

-- ------------------------------------------------------------------------

prop_unfoldHashable_outSig :: Property
prop_unfoldHashable_outSig =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(zdd :: ZDD o) ->
      ZDD.unfoldHashable ZDD.outSig zdd === zdd

-- ------------------------------------------------------------------------

prop_toGraph_fromGraph :: Property
prop_toGraph_fromGraph = do
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: ZDD o) ->
      ZDD.fromGraph (ZDD.toGraph a) === a

-- ------------------------------------------------------------------------
-- Test cases from JDD library
-- https://bitbucket.org/vahidi/jdd/src/21e103689c697fa40022294a829cab04add8ff79/src/jdd/zdd/ZDD.java

case_jdd_test_1 :: Assertion
case_jdd_test_1 = do
  let x1 = 1
      x2 = 2

      a, b, c, d, e, f, g :: ZDD ZDD.DescOrder
      a = ZDD.empty          -- {}
      b = ZDD.base           -- {{}}
      c = ZDD.change x1 b    -- {{x1}}
      d = ZDD.change x2 b    -- {{x2}}
      e = ZDD.union c d      -- {{x1}, {x2}}
      f = ZDD.union b e      -- {{}, {x1}, {x2}}
      g = ZDD.difference f c -- {{}, {x2}}

  -- directly from minatos paper, figure 9
  -- [until we find a better way to test isomorphism...]
  a @?= ZDD.Empty
  b @?= ZDD.Base
  c @?= ZDD.Branch x1 ZDD.empty ZDD.base
  d @?= ZDD.Branch x2 ZDD.empty ZDD.base
  e @?= ZDD.Branch x2 c ZDD.base
  f @?= ZDD.Branch x2 (ZDD.Branch x1 ZDD.base ZDD.base) ZDD.base
  g @?= ZDD.Branch x2 ZDD.base ZDD.base

  -- intersect
  ZDD.intersection a b @?= a
  ZDD.intersection a ZDD.base @?= a
  ZDD.intersection b b @?= b
  ZDD.intersection c e @?= c
  ZDD.intersection e f @?= e
  ZDD.intersection e g @?= d

  -- union
  ZDD.union a a @?= a
  ZDD.union b b @?= b
  ZDD.union a b @?= b
  ZDD.union g e @?= f

  -- diff
  ZDD.difference a a @?= a
  ZDD.difference b b @?= a
  ZDD.difference d c @?= d
  ZDD.difference c d @?= c
  ZDD.difference e c @?= d
  ZDD.difference e d @?= c
  ZDD.difference g b @?= d

  ZDD.difference g d @?= b
  ZDD.difference f g @?= c
  ZDD.difference f e @?= b

  -- subset0
  ZDD.subset0 x1 b @?= b
  ZDD.subset0 x2 b @?= b
  ZDD.subset0 x2 d @?= a
  ZDD.subset0 x2 e @?= c

  -- subset1
  ZDD.subset1 x1 b @?= ZDD.empty
  ZDD.subset1 x2 b @?= ZDD.empty
  ZDD.subset1 x2 d @?= b
  ZDD.subset1 x2 g @?= b
  ZDD.subset1 x1 g @?= a
  ZDD.subset1 x2 e @?= b

case_jdd_test_2 :: Assertion
case_jdd_test_2 = do
  let [a, b, c, d] = [4, 3, 2, 1]

  -- this is the exact construction sequence of Fig.14 in "Zero-suppressed BDDs and their application" by Minato
  let fig14 :: ZDD ZDD.DescOrder
      fig14 = ZDD.union z00__ z0100
        where
          z0000 = ZDD.base
          z000_ = ZDD.union z0000 (ZDD.change d z0000)
          z00__ = ZDD.union z000_ (ZDD.change c z000_)
          z0100 = ZDD.change b z0000

  -- this is the exact construction sequence of Fig.13 in "Zero-suppressed BDDs and their application" by Minato
  let fig13 :: ZDD ZDD.DescOrder
      fig13 = ZDD.intersection z0___ tmp
        where
          z___0 = ZDD.subsets (IntSet.fromList [a, b, c])
          z__0_ = ZDD.subsets (IntSet.fromList [a, b, d])
          z_0__ = ZDD.subsets (IntSet.fromList [a, c, d])
          z0___ = ZDD.subsets (IntSet.fromList [b, c, d])
          z__00 = ZDD.intersection z___0 z__0_
          tmp = ZDD.union z_0__ z__00

  fig14 @?= fig13

case_jdd_test_3 :: Assertion
case_jdd_test_3 = do
  let tmp :: ZDD ZDD.DescOrder
      tmp  = ZDD.fromListOfIntSets $ map IntSet.fromList [[2], [0,1], [1]] -- "100 011 010"
      tmp2 = ZDD.union (ZDD.singleton (IntSet.fromList [0, 1])) ZDD.base   -- union("11", base)
  -- 1. INTERSECT
  ZDD.intersection tmp tmp2 @?= ZDD.singleton (IntSet.fromList [0, 1])
  -- 2. UNION
  ZDD.union tmp tmp2 @?= ZDD.union tmp ZDD.base
  -- 3. DIFF
  ZDD.difference tmp tmp2 @?= ZDD.fromListOfIntSets (map IntSet.fromList [[1], [2]])

-- ------------------------------------------------------------------------

subsetOf :: IntSet -> Gen IntSet
subsetOf = liftM IntSet.fromList . sublistOf . IntSet.toList

arbitrarySmallIntMap :: Arbitrary a => Gen (IntMap a)
arbitrarySmallIntMap = do
  n <- choose (0, 12)
  liftM IntMap.fromList $ replicateM n $ do
    k <- arbitrary
    v <- arbitrary
    return (k, v)

-- ------------------------------------------------------------------------

zddTestGroup :: TestTree
zddTestGroup = $(testGroupGenerator)
