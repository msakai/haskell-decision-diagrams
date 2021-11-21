{-# OPTIONS_GHC -Wall -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module TestBDD (bddTestGroup) where

import Control.Monad
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import Data.List
import Data.Proxy
import qualified Data.Set as Set
import System.IO.Unsafe
import Test.QuickCheck.Function (apply)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.TH

import Data.DecisionDiagram.BDD (BDD (..), ItemOrder (..))
import qualified Data.DecisionDiagram.BDD as BDD

import Utils

-- ------------------------------------------------------------------------

instance BDD.ItemOrder a => Arbitrary (BDD a) where
  arbitrary = arbitraryBDDOver =<< arbitrary

  shrink (BDD.Leaf _) = []
  shrink (BDD.Branch x p0 p1) =
    [p0, p1]
    ++
    [ BDD.Branch x p0' p1'
    | (p0', p1') <- shrink (p0, p1), p0' /= p1'
    ]

arbitraryBDDOver :: forall a. BDD.ItemOrder a => IntSet -> Gen (BDD a)
arbitraryBDDOver xs = do
  let f vs n = oneof $
        [ return BDD.true
        , return BDD.false
        ]
        ++
        [ do v <- elements vs
             let vs' = dropWhile (\v' -> compareItem (Proxy :: Proxy a) v' v  /= GT) vs
             lo <- f vs' (n `div` 2)
             hi <- f vs' (n `div` 2) `suchThat` (/= lo)
             return (BDD.Branch v lo hi)
        | n > 0, not (null vs)
        ]
  sized $ f (sortBy (BDD.compareItem (Proxy :: Proxy a)) $ IntSet.toList xs)

arbitrarySatisfyingAssignment :: forall a. BDD.ItemOrder a => BDD a -> IntSet -> Gen (IntMap Bool)
arbitrarySatisfyingAssignment bdd xs = do
  m1 <- arbitrarySatisfyingPartialAssignment bdd
  let ys = xs `IntSet.difference` IntMap.keysSet m1
  m2 <- liftM(IntMap.fromAscList) $ forM (IntSet.toAscList ys) $ \y -> do
    v <- arbitrary
    return (y,v)
  return $ m1 `IntMap.union` m2

arbitrarySatisfyingPartialAssignment :: forall a. BDD.ItemOrder a => BDD a -> Gen (IntMap Bool)
arbitrarySatisfyingPartialAssignment = f
  where
    f (BDD.Leaf True) = return IntMap.empty
    f (BDD.Leaf False) = undefined
    f (BDD.Branch x lo hi) = oneof $
      [liftM (IntMap.insert x False) (f lo) | lo /= BDD.Leaf False]
      ++
      [liftM (IntMap.insert x True) (f hi) | hi /= BDD.Leaf False]

-- ------------------------------------------------------------------------
-- conjunction
-- ------------------------------------------------------------------------

prop_and_unitL :: Property
prop_and_unitL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (BDD.true BDD..&&. a) === a

prop_and_unitR :: Property
prop_and_unitR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..&&. BDD.true) === a

prop_and_falseL :: Property
prop_and_falseL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (BDD.false BDD..&&. a) === BDD.false

prop_and_falseR :: Property
prop_and_falseR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..&&. BDD.false) === BDD.false

prop_and_comm :: Property
prop_and_comm =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a BDD..&&. b) === (b BDD..&&. a)

prop_and_assoc :: Property
prop_and_assoc =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      (a BDD..&&. (b BDD..&&. c)) === ((a BDD..&&. b) BDD..&&. c)

prop_and_idempotent :: Property
prop_and_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..&&. a) === a

-- ------------------------------------------------------------------------
-- disjunction
-- ------------------------------------------------------------------------

prop_or_unitL :: Property
prop_or_unitL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (BDD.false BDD..||. a) === a

prop_or_unitR :: Property
prop_or_unitR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..||. BDD.false) === a

prop_or_trueL :: Property
prop_or_trueL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (BDD.true BDD..||. a) === BDD.true

prop_or_trueR :: Property
prop_or_trueR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..||. BDD.true) === BDD.true

prop_or_comm :: Property
prop_or_comm =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a BDD..||. b) === (b BDD..||. a)

prop_or_assoc :: Property
prop_or_assoc =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      (a BDD..||. (b BDD..||. c)) === ((a BDD..||. b) BDD..||. c)

prop_or_idempotent :: Property
prop_or_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..||. a) === a

-- ------------------------------------------------------------------------
-- xor
-- ------------------------------------------------------------------------

prop_xor_unitL :: Property
prop_xor_unitL =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (BDD.false `BDD.xor` a) === a

prop_xor_unitR :: Property
prop_xor_unitR =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a `BDD.xor` BDD.false) === a

prop_xor_comm :: Property
prop_xor_comm =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a `BDD.xor` b) === (b `BDD.xor` a)

prop_xor_assoc :: Property
prop_xor_assoc =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      (a `BDD.xor` (b `BDD.xor` c)) === ((a `BDD.xor` b) `BDD.xor` c)

prop_xor_involution :: Property
prop_xor_involution =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a `BDD.xor` a) === BDD.false

prop_xor_dist :: Property
prop_xor_dist =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      (a BDD..&&. (b `BDD.xor` c)) === ((a BDD..&&. b) `BDD.xor` (a BDD..&&. c))

-- ------------------------------------------------------------------------
-- distributivity
-- ------------------------------------------------------------------------

prop_dist_1 :: Property
prop_dist_1 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      (a BDD..&&. (b BDD..||. c)) === ((a BDD..&&. b) BDD..||. (a BDD..&&. c))

prop_dist_2 :: Property
prop_dist_2 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      (a BDD..||. (b BDD..&&. c)) === ((a BDD..||. b) BDD..&&. (a BDD..||. c))

prop_absorption_1 :: Property
prop_absorption_1 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a BDD..&&. (a BDD..||. b)) === a

prop_absorption_2 :: Property
prop_absorption_2 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a BDD..||. (a BDD..&&. b)) === a

-- ------------------------------------------------------------------------
-- negation
-- ------------------------------------------------------------------------

prop_double_negation :: Property
prop_double_negation =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.notB (BDD.notB a) === a

prop_and_complement :: Property
prop_and_complement =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..&&. BDD.notB a) === BDD.false

prop_or_complement :: Property
prop_or_complement =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a BDD..||. BDD.notB a) === BDD.true

prop_de_morgan_1 :: Property
prop_de_morgan_1 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      BDD.notB (a BDD..||. b) === (BDD.notB a BDD..&&. BDD.notB b)

prop_de_morgan_2 :: Property
prop_de_morgan_2 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      BDD.notB (a BDD..&&. b) === (BDD.notB a BDD..||. BDD.notB b)

-- ------------------------------------------------------------------------
-- Implication
-- ------------------------------------------------------------------------

prop_imply :: Property
prop_imply =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a BDD..=>. b) === (BDD.notB a BDD..||. b)

prop_imply_currying :: Property
prop_imply_currying =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b, c) ->
      ((a BDD..&&. b) BDD..=>. c) === (a BDD..=>. (b BDD..=>. c))

-- ------------------------------------------------------------------------
-- Equivalence
-- ------------------------------------------------------------------------

prop_equiv :: Property
prop_equiv =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      (a BDD..<=>. b) === ((a BDD..=>. b) BDD..&&. (b BDD..=>. a))

-- ------------------------------------------------------------------------
-- If-then-else
-- ------------------------------------------------------------------------

prop_ite :: Property
prop_ite =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(c :: BDD o, t, e) ->
      BDD.ite c t e === ((c BDD..&&. t) BDD..||. (BDD.notB c BDD..&&. e))

prop_ite_swap_branch :: Property
prop_ite_swap_branch =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(c :: BDD o, t, e) ->
      BDD.ite c t e === BDD.ite (BDD.notB c) e t

prop_ite_dist_not :: Property
prop_ite_dist_not =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(c :: BDD o, t, e) ->
      BDD.notB (BDD.ite c t e) === BDD.ite c (BDD.notB t) (BDD.notB e)

prop_ite_dist_and :: Property
prop_ite_dist_and =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(c :: BDD o, t, e, d) ->
      (d BDD..&&. BDD.ite c t e) === BDD.ite c (d BDD..&&. t) (d BDD..&&. e)

prop_ite_dist_or :: Property
prop_ite_dist_or =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(c :: BDD o, t, e, d) ->
      (d BDD..||. BDD.ite c t e) === BDD.ite c (d BDD..||. t) (d BDD..||. e)

-- ------------------------------------------------------------------------
-- Pseudo-Boolean
-- ------------------------------------------------------------------------

prop_pbAtLeast :: Property
prop_pbAtLeast =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        let a :: BDD o
            a = BDD.pbAtLeast xs k
         in counterexample (show a) $
              if a == BDD.Leaf False then
                property (k > sum [max 0 w | (_,w) <- IntMap.toList xs])
              else
                forAll (arbitrarySatisfyingAssignment a (IntMap.keysSet xs)) $ \ys ->
                  (IntMap.keysSet ys `IntSet.isSubsetOf` IntMap.keysSet xs)
                  .&&.
                  sum [xs IntMap.! y | (y,b) <- IntMap.toList ys, b] >= k

prop_pbAtMost :: Property
prop_pbAtMost =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        let a :: BDD o
            a = BDD.pbAtMost xs k
         in counterexample (show a) $
              if a == BDD.Leaf False then
                property (k < sum [min 0 w | (_,w) <- IntMap.toList xs])
              else
                forAll (arbitrarySatisfyingAssignment a (IntMap.keysSet xs)) $ \ys ->
                  (IntMap.keysSet ys `IntSet.isSubsetOf` IntMap.keysSet xs)
                  .&&.
                  sum [xs IntMap.! y | (y,b) <- IntMap.toList ys, b] <= k

prop_pbExactly :: Property
prop_pbExactly =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        let a :: BDD o
            a = BDD.pbExactly xs k
         in counterexample (show a) $
              if a == BDD.Leaf False then
                property True
              else
                forAll (arbitrarySatisfyingAssignment a (IntMap.keysSet xs)) $ \ys ->
                  (IntMap.keysSet ys `IntSet.isSubsetOf` IntMap.keysSet xs)
                  .&&.
                  sum [xs IntMap.! y | (y,b) <- IntMap.toList ys, b] === k

prop_pbExactly_2 :: Property
prop_pbExactly_2 =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll (gen xs) $ \(m, k) ->
        let a :: BDD o
            a = BDD.pbExactly xs k
         in counterexample (show a) $ BDD.evaluate (m IntMap.!) a
  where
    gen :: IntMap Integer -> Gen (IntMap Bool, Integer)
    gen xs = do
      ys <- sublistOf (IntMap.toList xs)
      let ys' = IntSet.fromList [y | (y,_) <- ys]
      return
        ( IntMap.mapWithKey (\x _ -> x `IntSet.member` ys') xs
        , sum [w | (_,w) <- ys]
        )

prop_pbExactlyIntegral :: Property
prop_pbExactlyIntegral =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntMap $ \(xs :: IntMap Integer) ->
      forAll arbitrary $ \k ->
        (BDD.pbExactlyIntegral xs k :: BDD o) === BDD.pbExactly xs k

-- ------------------------------------------------------------------------
-- Quantification
-- ------------------------------------------------------------------------

prop_forAll :: Property
prop_forAll =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      BDD.forAll x a === (BDD.restrict x True a BDD..&&. BDD.restrict x False a)

prop_exists :: Property
prop_exists =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      BDD.exists x a === (BDD.restrict x True a BDD..||. BDD.restrict x False a)

prop_existsUnique :: Property
prop_existsUnique =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      BDD.existsUnique x a === (BDD.restrict x True a `BDD.xor` BDD.restrict x False a)

prop_forAll_support :: Property
prop_forAll_support =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      let b = BDD.forAll x a
          xs = BDD.support b
       in counterexample (show (b, xs)) $
            x `IntSet.notMember` xs

prop_exists_support :: Property
prop_exists_support =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      let b = BDD.exists x a
          xs = BDD.support b
       in counterexample (show (b, xs)) $
            x `IntSet.notMember` xs

prop_existsUnique_support :: Property
prop_existsUnique_support =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      let b = BDD.existsUnique x a
          xs = BDD.support b
       in counterexample (show (b, xs)) $
            x `IntSet.notMember` xs

-- ------------------------------------------------------------------------

prop_forAllSet_empty :: Property
prop_forAllSet_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.forAllSet IntSet.empty a === a

prop_existsSet_empty :: Property
prop_existsSet_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.existsSet IntSet.empty a === a

prop_existsUniqueSet_empty :: Property
prop_existsUniqueSet_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.existsUniqueSet IntSet.empty a === a

prop_forAllSet_singleton :: Property
prop_forAllSet_singleton =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      BDD.forAllSet (IntSet.singleton x) a === BDD.forAll x a

prop_existsSet_singleton :: Property
prop_existsSet_singleton =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      BDD.existsSet (IntSet.singleton x) a === BDD.exists x a

prop_existsUniqueSet_singleton :: Property
prop_existsUniqueSet_singleton =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x, a :: BDD o) ->
      BDD.existsUniqueSet (IntSet.singleton x) a === BDD.existsUnique x a

prop_forAllSet_union :: Property
prop_forAllSet_union =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(xs1, xs2, a :: BDD o) ->
      BDD.forAllSet (xs1 `IntSet.union` xs2) a === BDD.forAllSet xs2 (BDD.forAllSet xs1 a)

prop_existsSet_union :: Property
prop_existsSet_union =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(xs1, xs2, a :: BDD o) ->
      BDD.existsSet (xs1 `IntSet.union` xs2) a === BDD.existsSet xs2 (BDD.existsSet xs1 a)

prop_existsUniqueSet_union :: Property
prop_existsUniqueSet_union =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitraryDisjointSets $ \(xs1, xs2) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.existsUniqueSet (xs1 `IntSet.union` xs2) a === BDD.existsUniqueSet xs2 (BDD.existsUniqueSet xs1 a)
  where
    arbitraryDisjointSets = do
      (u, v) <- arbitrary
      return (u `IntSet.intersection` v, u IntSet.\\ v)

-- ------------------------------------------------------------------------

case_fold_laziness :: Assertion
case_fold_laziness = do
  let bdd :: BDD BDD.AscOrder
      bdd = BDD.Branch 0 (BDD.Branch 1 (BDD.Leaf False) (BDD.Leaf True)) (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True))
      f x lo _hi =
        if x == 2 then
          error "unused value should not be evaluated"
        else
          lo
  seq (BDD.fold False True f bdd) $ return ()

case_fold'_strictness :: Assertion
case_fold'_strictness = do
  ref <- newIORef False
  let bdd :: BDD BDD.AscOrder
      bdd = BDD.Branch 0 (BDD.Branch 1 (BDD.Leaf False) (BDD.Leaf True)) (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True))
      f x lo _hi = unsafePerformIO $ do
        when (x==2) $ writeIORef ref True
        return lo
  seq (BDD.fold' False True f bdd) $ do
    flag <- readIORef ref
    assertBool "unused value should be evaluated" flag

-- ------------------------------------------------------------------------

case_support_false :: Assertion
case_support_false = BDD.support BDD.false @?= IntSet.empty

case_support_true :: Assertion
case_support_true = BDD.support BDD.true @?= IntSet.empty

prop_support_var :: Property
prop_support_var =
  forAll arbitrary $ \x ->
    BDD.support (BDD.var x) === IntSet.singleton x

prop_support_not :: Property
prop_support_not =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      let lhs = BDD.support a
          rhs = BDD.support (BDD.notB a)
       in lhs === rhs

prop_support_and :: Property
prop_support_and =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      let lhs = BDD.support (a BDD..&&. b)
          rhs = BDD.support a `IntSet.union` BDD.support b
       in counterexample (show (lhs, rhs)) $ lhs `IntSet.isSubsetOf` rhs

prop_support_or :: Property
prop_support_or =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      let lhs = BDD.support (a BDD..||. b)
          rhs = BDD.support a `IntSet.union` BDD.support b
       in counterexample (show (lhs, rhs)) $ lhs `IntSet.isSubsetOf` rhs

-- ------------------------------------------------------------------------

prop_evaluate_var :: Property
prop_evaluate_var =
 forAll arbitrary $ \(f' :: Fun Int Bool) ->
   let f = apply f'
    in forAllItemOrder $ \(_ :: Proxy o) ->
         forAll arbitrary $ \x ->
           BDD.evaluate f (BDD.var x :: BDD o) === f x

prop_evaluate_not :: Property
prop_evaluate_not =
 forAll arbitrary $ \(f' :: Fun Int Bool) ->
   let f = apply f'
    in forAllItemOrder $ \(_ :: Proxy o) ->
         forAll arbitrary $ \(a :: BDD o) ->
           BDD.evaluate f (BDD.notB a) === not (BDD.evaluate f a)

prop_evaluate_and :: Property
prop_evaluate_and =
 forAll arbitrary $ \(f' :: Fun Int Bool) ->
   let f = apply f'
    in forAllItemOrder $ \(_ :: Proxy o) ->
         forAll arbitrary $ \(a :: BDD o, b) ->
           BDD.evaluate f (a BDD..&&. b) === (BDD.evaluate f a && BDD.evaluate f b)

prop_evaluate_or :: Property
prop_evaluate_or =
 forAll arbitrary $ \(f' :: Fun Int Bool) ->
   let f = apply f'
    in forAllItemOrder $ \(_ :: Proxy o) ->
         forAll arbitrary $ \(a :: BDD o, b) ->
           BDD.evaluate f (a BDD..||. b) === (BDD.evaluate f a || BDD.evaluate f b)

-- ------------------------------------------------------------------------

prop_restrict :: Property
prop_restrict =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \x ->
        let b = (BDD.var x BDD..&&. BDD.restrict x True a) BDD..||.
                (BDD.notB (BDD.var x) BDD..&&. BDD.restrict x False a)
         in a === b

prop_restrict_idempotent :: Property
prop_restrict_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \(x, val) ->
        let b = BDD.restrict x val a
            c = BDD.restrict x val b
         in counterexample (show (b, c)) $ b === c

prop_restrict_not :: Property
prop_restrict_not =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \(x, val) ->
        BDD.restrict x val (BDD.notB a) === BDD.notB (BDD.restrict x val a)

prop_restrict_and :: Property
prop_restrict_and =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      forAll arbitrary $ \(x, val) ->
        BDD.restrict x val (a BDD..&&. b) === (BDD.restrict x val a BDD..&&. BDD.restrict x val b)

prop_restrict_or :: Property
prop_restrict_or =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      forAll arbitrary $ \(x, val) ->
        BDD.restrict x val (a BDD..||. b) === (BDD.restrict x val a BDD..||. BDD.restrict x val b)

prop_restrict_var :: Property
prop_restrict_var =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \x ->
      let a :: BDD o
          a = BDD.var x
       in (BDD.restrict x True a === BDD.true) .&&.
          (BDD.restrict x False a === BDD.false)

prop_restrict_support :: Property
prop_restrict_support =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \(x, val) ->
        let b = BDD.restrict x val a
            xs = BDD.support b
         in counterexample (show b) $
            counterexample (show xs) $
              x `IntSet.notMember` xs

-- ------------------------------------------------------------------------

prop_restrictSet_empty :: Property
prop_restrictSet_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.restrictSet IntMap.empty a === a

prop_restrictSet_singleton :: Property
prop_restrictSet_singleton =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \(x, val) ->
        BDD.restrict x val a === BDD.restrictSet (IntMap.singleton x val) a

prop_restrictSet_union :: Property
prop_restrictSet_union =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \(val1, val2) ->
        and (IntMap.intersectionWith (==) val1 val2)
        ==>
        (BDD.restrictSet val2 (BDD.restrictSet val1 a) === BDD.restrictSet (val1 `IntMap.union` val2) a)

prop_restrictSet_idempotent :: Property
prop_restrictSet_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \val ->
        let b = BDD.restrictSet val a
            c = BDD.restrictSet val b
         in counterexample (show (b, c)) $ b === c

prop_restrictSet_not :: Property
prop_restrictSet_not =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \val ->
        BDD.restrictSet val (BDD.notB a) === BDD.notB (BDD.restrictSet val a)

prop_restrictSet_and :: Property
prop_restrictSet_and =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      forAll arbitrary $ \val ->
        BDD.restrictSet val (a BDD..&&. b) === (BDD.restrictSet val a BDD..&&. BDD.restrictSet val b)

prop_restrictSet_or :: Property
prop_restrictSet_or =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      forAll arbitrary $ \val ->
        BDD.restrictSet val (a BDD..||. b) === (BDD.restrictSet val a BDD..||. BDD.restrictSet val b)

-- ------------------------------------------------------------------------

prop_restrictLaw :: Property
prop_restrictLaw =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \law ->
        (law BDD..&&. BDD.restrictLaw law a) === (law BDD..&&. a)

case_restrictLaw_case_0 :: Assertion
case_restrictLaw_case_0 = (law BDD..&&. BDD.restrictLaw law a) @?= (law BDD..&&. a)
  where
    a, law :: BDD BDD.AscOrder
    a = BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True)
    law = BDD.Branch 1 (BDD.Branch 2 (BDD.Leaf True) (BDD.Leaf False)) (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True))

prop_restrictLaw_true :: Property
prop_restrictLaw_true =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.restrictLaw BDD.true a === a

prop_restrictLaw_self :: Property
prop_restrictLaw_self =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a /= BDD.false) ==> BDD.restrictLaw a a === BDD.true

prop_restrictLaw_not_self :: Property
prop_restrictLaw_not_self =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      (a /= BDD.true) ==> BDD.restrictLaw (BDD.notB a) a === BDD.false

prop_restrictLaw_restrictSet :: Property
prop_restrictLaw_restrictSet =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \val ->
        let b = BDD.andB [if v then BDD.var x else BDD.notB (BDD.var x) | (x,v) <- IntMap.toList val]
         in BDD.restrictLaw b a === BDD.restrictSet val a

-- prop_restrictLaw_and_condition :: Property
-- prop_restrictLaw_and_condition =
--   forAllItemOrder $ \(_ :: Proxy o) ->
--     forAll arbitrary $ \(a :: BDD o) ->
--       forAll arbitrary $ \(val1, val2) ->
--         let val = val1 BDD..&&. val2
--          in counterexample (show val) $
--               (val /= BDD.false)
--               ==>
--               (BDD.restrictLaw val a === BDD.restrictLaw val2 (BDD.restrictLaw val1 a))

-- counterexample to the above prop_restrictLaw_and_condition
case_restrictLaw_case_1 :: Assertion
case_restrictLaw_case_1 = do
  -- BDD.restrictLaw val a @?= BDD.restrictLaw val2 (BDD.restrictLaw val1 a)
  BDD.restrictLaw val a @?= BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True)
  BDD.restrictLaw val2 (BDD.restrictLaw val1 a) @?= BDD.Branch 1 (BDD.Leaf True) (Branch 2 (BDD.Leaf False) (BDD.Leaf True))
  where
    a :: BDD BDD.AscOrder
    a = Branch 2 (BDD.Leaf False) (BDD.Leaf True) -- x2
    val1 = BDD.Branch 1 (BDD.Leaf False) (BDD.Leaf True) -- x1
    val2 = BDD.Branch 1 (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True)) (BDD.Leaf True) -- x1 ∨ x2
    val = val1 BDD..&&. val2 -- x1

prop_restrictLaw_or_condition :: Property
prop_restrictLaw_or_condition =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \(val1, val2) ->
        let val = val1 BDD..||. val2
         in counterexample (show val) $
              (val BDD..&&. BDD.restrictLaw val a) === (val1 BDD..&&. BDD.restrictLaw val1 a BDD..||. val2 BDD..&&. BDD.restrictLaw val2 a)

prop_restrictLaw_idempotent :: Property
prop_restrictLaw_idempotent =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll arbitrary $ \val ->
        let b = BDD.restrictLaw val a
            c = BDD.restrictLaw val b
         in counterexample (show (b, c)) $ b === c

prop_restrictLaw_not :: Property
prop_restrictLaw_not =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      forAll (arbitrary `suchThat` (/= BDD.false)) $ \val ->
        BDD.restrictLaw val (BDD.notB a) === BDD.notB (BDD.restrictLaw val a)

prop_restrictLaw_and :: Property
prop_restrictLaw_and =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      forAll (arbitrary `suchThat` (/= BDD.false)) $ \val ->
        BDD.restrictLaw val (a BDD..&&. b) === (BDD.restrictLaw val a BDD..&&. BDD.restrictLaw val b)

prop_restrictLaw_or :: Property
prop_restrictLaw_or =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o, b) ->
      forAll (arbitrary `suchThat` (/= BDD.false)) $ \val ->
        BDD.restrictLaw val (a BDD..||. b) === (BDD.restrictLaw val a BDD..||. BDD.restrictLaw val b)

-- prop_restrictLaw_minimality :: Property
-- prop_restrictLaw_minimality =
--   forAllItemOrder $ \(_ :: Proxy o) ->
--     forAll arbitrary $ \(a :: BDD o) ->
--       forAll arbitrary $ \law ->
--         let b = BDD.restrictLaw law a
--          in counterexample (show b) $
--               ((law BDD..&&. b) === (law BDD..&&. a))
--               .&&.
--               conjoin [counterexample (show b') $ (law BDD..&&. b') =/= (law BDD..&&. a) | b' <- shrink b]

case_restrictLaw_non_minimal_1 :: Assertion
case_restrictLaw_non_minimal_1 = do
  (law BDD..&&. BDD.restrictLaw law a) @?= (law BDD..&&. a)
  BDD.restrictLaw law a @?= b -- should be 'a'?
  where
    law, a :: BDD BDD.AscOrder
    law = BDD.Branch 1 (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True)) (BDD.Leaf True) -- x1 ∨ x2
    a = BDD.Branch 2 (BDD.Leaf True) (BDD.Leaf False) -- ¬x2
    b = BDD.Branch 1 (BDD.Leaf False) (BDD.Branch 2 (BDD.Leaf True) (BDD.Leaf False)) -- x1 ∧ ¬x2

case_restrictLaw_non_minimal_2 :: Assertion
case_restrictLaw_non_minimal_2 = do
  (law BDD..&&. BDD.restrictLaw law a) @?= (law BDD..&&. a)
  BDD.restrictLaw law a @?= b -- should be 'a'?
  where
    law, a, b :: BDD BDD.AscOrder
    law = BDD.Branch 1 (BDD.Leaf True) (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True)) -- ¬x1 ∨ x2
    a = BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True) -- x2
    b = BDD.Branch 1 (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True)) (BDD.Leaf True) -- x1 ∨ x2

-- ------------------------------------------------------------------------

prop_subst_restrict_constant :: Property
prop_subst_restrict_constant =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll arbitrary $ \x ->
    forAll arbitrary $ \val ->
      BDD.subst x (if val then BDD.true else BDD.false) m === BDD.restrict x val m

prop_subst_restrict :: Property
prop_subst_restrict =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll arbitrary $ \x ->
    forAll arbitrary $ \(n :: BDD o) ->
      BDD.subst x n m === ((n BDD..&&. BDD.restrict x True m) BDD..||. (BDD.notB n BDD..&&. BDD.restrict x False m))

prop_subst_same_var :: Property
prop_subst_same_var =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll arbitrary $ \x ->
      BDD.subst x (BDD.var x) m === m

prop_subst_not_occured :: Property
prop_subst_not_occured =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll (arbitrary `suchThat` (\x -> x `IntSet.notMember` (BDD.support m))) $ \x ->
    forAll arbitrary $ \(n :: BDD o) ->
      BDD.subst x n m === m

-- If x1≠x2 and x1∉FV(M2) then M[x1 ↦ M1][x2 ↦ M2] = M[x2 ↦ M2][x1 ↦ M1[x2 ↦ M2]].
prop_subst_dist :: Property
prop_subst_dist =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(x1, m1) ->
    forAll ((,) <$> (arbitrary `suchThat` (/= x1)) <*> (arbitrary `suchThat` (\m2 -> x1 `IntSet.notMember` BDD.support m2))) $ \(x2, m2) ->
    forAll arbitrary $ \(m :: BDD o) ->
      BDD.subst x2 m2 (BDD.subst x1 m1 m) === BDD.subst x1 (BDD.subst x2 m2 m1) (BDD.subst x2 m2 m)

-- ------------------------------------------------------------------------

prop_substSet_empty :: Property
prop_substSet_empty =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
      BDD.substSet IntMap.empty m === m

prop_substSet_singleton :: Property
prop_substSet_singleton =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll arbitrary $ \x ->
    forAll arbitrary $ \m1 ->
      BDD.substSet (IntMap.singleton x m1) m === BDD.subst x m1 m

case_substSet_case_1 :: Assertion
case_substSet_case_1 = do
  BDD.substSet (IntMap.singleton x m1) m @?= BDD.subst x m1 m
  where
    m :: BDD BDD.AscOrder
    m = BDD.Branch 1 (BDD.Branch 2 (BDD.Leaf True) (BDD.Leaf False)) (BDD.Branch 2 (BDD.Leaf False) (BDD.Leaf True))
    x = 1
    m1 = BDD.Branch 1 (BDD.Leaf True) (BDD.Leaf False)

prop_substSet_same_vars :: Property
prop_substSet_same_vars =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll arbitrary $ \xs ->
      BDD.substSet (IntMap.fromAscList [(x, BDD.var x) | x <- IntSet.toAscList xs]) m === m

prop_substSet_not_occured :: Property
prop_substSet_not_occured =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(m :: BDD o) ->
    forAll (f (BDD.support m)) $ \s ->
      BDD.substSet s m === m
  where
    f xs = liftM IntMap.fromList $ listOf $ do
      y <- arbitrary `suchThat` (`IntSet.notMember` xs)
      m <- arbitrary
      return (y, m)

prop_substSet_compose :: Property
prop_substSet_compose =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
    forAll arbitrary $ \ys ->
    forAll (liftM IntMap.fromList $ mapM (\x -> (,) <$> pure x <*> arbitraryBDDOver ys) (IntSet.toList xs)) $ \s1 ->
    forAll (liftM IntMap.fromList $ mapM (\y -> (,) <$> pure y <*> arbitrary) (IntSet.toList ys)) $ \s2 ->
    forAll (arbitraryBDDOver xs) $ \(m :: BDD o) ->
      BDD.substSet s2 (BDD.substSet s1 m) === BDD.substSet (IntMap.map (BDD.substSet s2) s1) m

case_substSet_case_2 :: Assertion
case_substSet_case_2 = do
  let m :: BDD BDD.AscOrder
      m = BDD.var 1 BDD..&&. BDD.var 2
  BDD.substSet (IntMap.fromList [(1, BDD.var 2), (2, BDD.var 3)]) m @?= BDD.var 2 BDD..&&. BDD.var 3
  BDD.substSet (IntMap.fromList [(1, BDD.var 3), (2, BDD.var 1)]) m @?= BDD.var 3 BDD..&&. BDD.var 1

-- ------------------------------------------------------------------------

data MonotoneExpr a
  = MVar a
  | MAnd (MonotoneExpr a) (MonotoneExpr a)
  | MOr (MonotoneExpr a) (MonotoneExpr a)
  | MConst Bool
  deriving (Show)

arbitraryMonotoneExpr :: forall a. Gen a -> Gen (MonotoneExpr a)
arbitraryMonotoneExpr gen = sized f
  where
    f :: Int -> Gen (MonotoneExpr a)
    f n = oneof $
      [ liftM MConst arbitrary
      , liftM MVar gen
      ]
      ++
      concat
      [ [liftM2 MAnd sub sub, liftM2 MOr sub sub]
      | n > 0, let sub = f (n `div` 2)
      ]

evalMonotoneExpr :: ItemOrder a => (b -> BDD a) -> MonotoneExpr b -> BDD a
evalMonotoneExpr f = g
  where
    g (MVar a) = f a
    g (MConst v) = BDD.Leaf v
    g (MOr a b) = g a BDD..||. g b
    g (MAnd a b) = g a BDD..&&. g b

forAllMonotonicFunction :: forall o prop. (ItemOrder o, Testable prop) => IntSet -> ((BDD o -> BDD o) -> prop) -> Property
forAllMonotonicFunction xs k =
  forAll (arbitraryMonotoneExpr (elements (Nothing : map Just (IntSet.toList xs)))) $ \e -> do
    let f :: BDD o -> BDD o
        f x = evalMonotoneExpr g e
          where
            g Nothing = x
            g (Just v) = BDD.var v
     in k f

prop_lfp_is_fixed_point :: Property
prop_lfp_is_fixed_point =
 forAll arbitrary $ \(xs :: IntSet) ->
   forAllItemOrder $ \(_ :: Proxy o) ->
     forAllMonotonicFunction xs $ \(f :: BDD o -> BDD o) -> do
       let a = BDD.lfp f
        in counterexample (show a) $ f a === a


prop_gfp_is_fixed_point :: Property
prop_gfp_is_fixed_point =
 forAll arbitrary $ \(xs :: IntSet) ->
   forAllItemOrder $ \(_ :: Proxy o) ->
     forAllMonotonicFunction xs $ \(f :: BDD o -> BDD o) -> do
       let a = BDD.gfp f
        in counterexample (show a) $ f a === a

prop_lfp_imply_gfp :: Property
prop_lfp_imply_gfp =
 forAll arbitrary $ \(xs :: IntSet) ->
   forAllItemOrder $ \(_ :: Proxy o) ->
     forAllMonotonicFunction xs $ \(f :: BDD o -> BDD o) -> do
       let a = BDD.lfp f
           b = BDD.gfp f
        in counterexample (show (a, b)) $ (a BDD..=>. b) === BDD.true

-- ------------------------------------------------------------------------

prop_anySat :: Property
prop_anySat =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(bdd :: BDD o) ->
      case BDD.anySat bdd of
        Just p -> counterexample (show p) $ BDD.evaluate (p IntMap.!) bdd
        Nothing -> bdd === BDD.Leaf False

prop_allSat :: Property
prop_allSat =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntSet $ \xs ->
      forAll (arbitraryBDDOver xs) $ \(bdd :: BDD o) ->
         let ps = BDD.allSat bdd
         in null ps === (bdd == BDD.Leaf False)
            .&&.
            conjoin [counterexample (show p) $ BDD.evaluate (p IntMap.!) bdd |  p <- ps]

prop_anySatComplete :: Property
prop_anySatComplete =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \xs ->
      forAll (arbitraryBDDOver xs) $ \(bdd :: BDD o) ->
        case BDD.anySatComplete xs bdd of
          Just p -> counterexample (show p) $
            IntMap.keysSet p === xs
            .&&.
            BDD.evaluate (p IntMap.!) bdd
          Nothing -> bdd === BDD.Leaf False

prop_allSatComplete :: Property
prop_allSatComplete =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntSet $ \xs ->
      forAll (arbitraryBDDOver xs) $ \(bdd :: BDD o) ->
        let ps = BDD.allSatComplete xs bdd
            qs = [q | q <- foldM (\m x -> [IntMap.insert x v m | v <- [False, True]]) IntMap.empty (IntSet.toList xs)
                    , BDD.evaluate (q IntMap.!) bdd]
         in conjoin [counterexample (show p) (IntMap.keysSet p === xs) | p <- ps]
            .&&.
            Set.fromList ps === Set.fromList qs

prop_countSat_allSatComplete :: Property
prop_countSat_allSatComplete =
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrarySmallIntSet $ \xs ->
      forAll (arbitraryBDDOver xs) $ \(bdd :: BDD o) ->
        let ps = BDD.allSatComplete xs bdd
            n = BDD.countSat xs bdd
         in counterexample (show n) $
              if bdd == BDD.Leaf False then
                n === 0
              else
                -- Note that the number of partial assignments is smaller than the number of total assignments
                (n > 0) .&&. n === length ps

-- ------------------------------------------------------------------------

prop_toGraph_fromGraph :: Property
prop_toGraph_fromGraph = do
  forAllItemOrder $ \(_ :: Proxy o) ->
    forAll arbitrary $ \(a :: BDD o) ->
      BDD.fromGraph (BDD.toGraph a) === a

-- ------------------------------------------------------------------------

arbitrarySmallIntSet :: Gen IntSet
arbitrarySmallIntSet = do
  n <- choose (0, 12)
  liftM IntSet.fromList $ replicateM n arbitrary

arbitrarySmallIntMap :: Arbitrary a => Gen (IntMap a)
arbitrarySmallIntMap = do
  n <- choose (0, 12)
  liftM IntMap.fromList $ replicateM n $ do
    k <- arbitrary
    v <- arbitrary
    return (k, v)

-- ------------------------------------------------------------------------

bddTestGroup :: TestTree
bddTestGroup = $(testGroupGenerator)
