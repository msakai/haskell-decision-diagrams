{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.DecisionDiagram.BDD
-- Copyright   :  (c) Masahiro Sakai 2021
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
--
-- Reduced Ordered Binary Decision Diagrams (ROBDD) and its Zero-Suppressed variant.
--
-- References:
--
-- * Bryant, "Graph-Based Algorithms for Boolean Function Manipulation,"
--   in IEEE Transactions on Computers, vol. C-35, no. 8, pp. 677-691,
--   Aug. 1986, doi: [10.1109/TC.1986.1676819](https://doi.org/10.1109/TC.1986.1676819).
--   <https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf>
--
-- * S. Minato, "Zero-Suppressed BDDs for Set Manipulation in Combinatorial Problems,"
--   30th ACM/IEEE Design Automation Conference, 1993, pp. 272-277,
--   doi: [10.1145/157485.164890](https://doi.org/10.1145/157485.164890).
--   <https://www.researchgate.net/publication/221062015_Zero-Suppressed_BDDs_for_Set_Manipulation_in_Combinatorial_Problems>
--
----------------------------------------------------------------------
module Data.DecisionDiagram.BDD
  (
  -- * Item ordering
    ItemOrder (..)
  , DefaultOrder
  , withDefaultOrder
  , withCustomOrder

  -- * BDD
  , BDD (..)
  , bddTrue
  , bddFalse
  , bddVar
  , bddNot
  , bddAnd
  , bddOr

  -- * ZDD
  , ZDD (..)
  , zddEmpty
  , zddUnit
  , zddSubset1
  , zddSubset0
  , zddChange
  , zddUnion
  , zddIntersection
  , zddDifference
  , zddSize
  , zddToSetOfIntSets
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric.Natural

import Data.DecisionDiagram.BDD.Internal

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Reduced ordered binary decision diagram representing boolean function
newtype BDD a = BDD Node
  deriving (Hashable, Show)

bddNode :: Int -> Node -> Node -> Node
bddNode ind lo hi
  | lo == hi = lo
  | otherwise = Branch ind lo hi

-- | True
bddTrue :: BDD a
bddTrue = BDD T

-- | False
bddFalse :: BDD a
bddFalse = BDD F

-- | A variable \(x_i\)
bddVar :: Int -> BDD a
bddVar ind = BDD (Branch ind F T)

-- | Negation of a boolean function
bddNot :: BDD a -> BDD a
bddNot (BDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f T = return F
      f F = return T
      f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- liftM2 (bddNode ind) (f lo) (f hi)
            H.insert h n ret
            return ret
  ret <- f node
  return (BDD ret)

-- | Conjunction of two boolean function
bddAnd :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
bddAnd (BDD node1) (BDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f T b = return b
      f F _ = return F
      f a T = return a
      f _ F = return F
      f a b | a == b = return a
      f n1@(Branch ind1 lo1 hi1) n2@(Branch ind2 lo2 hi2) = do
        m <- H.lookup h (n1, n2)
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind1 ind2 of
              EQ -> liftM2 (bddNode ind1) (f lo1 lo2) (f hi1 hi2)
              LT -> liftM2 (bddNode ind1) (f lo1 n2) (f hi1 n2)
              GT -> liftM2 (bddNode ind2) (f n1 lo2) (f n1 hi2)
            H.insert h (n1, n2) ret
            return ret
  ret <- f node1 node2
  return (BDD ret)

-- | Disjunction of two boolean function
bddOr :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
bddOr (BDD node1) (BDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f T _ = return T
      f F b = return b
      f _ T = return T
      f a F = return a
      f a b | a == b = return a
      f n1@(Branch ind1 lo1 hi1) n2@(Branch ind2 lo2 hi2) = do
        m <- H.lookup h (n1, n2)
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind1 ind2 of
              EQ -> liftM2 (bddNode ind1) (f lo1 lo2) (f hi1 hi2)
              LT -> liftM2 (bddNode ind1) (f lo1 n2) (f hi1 n2)
              GT -> liftM2 (bddNode ind2) (f n1 lo2) (f n1 hi2)
            H.insert h (n1, n2) ret
            return ret
  ret <- f node1 node2
  return (BDD ret)

-- https://ja.wikipedia.org/wiki/%E4%BA%8C%E5%88%86%E6%B1%BA%E5%AE%9A%E5%9B%B3
_test_bdd :: BDD DefaultOrder
_test_bdd = (bddNot x1 `bddAnd` bddNot x2 `bddAnd` bddNot x3) `bddOr` (x1 `bddAnd` x2) `bddOr` (x2 `bddAnd` x3)
  where
    x1 = bddVar 1
    x2 = bddVar 2
    x3 = bddVar 3
{-
BDD (Node 880 (UBranch 1 (Node 611 (UBranch 2 (Node 836 UT) (Node 215 UF))) (Node 806 (UBranch 2 (Node 842 (UBranch 3 (Node 836 UT) (Node 215 UF))) (Node 464 (UBranch 3 (Node 215 UF) (Node 836 UT)))))))
-}

-- ------------------------------------------------------------------------

-- | Zero-suppressed binary decision diagram representing family of sets
newtype ZDD a = ZDD Node
  deriving (Hashable, Show)

zddNode :: Int -> Node -> Node -> Node
zddNode _ p0 F = p0
zddNode top p0 p1 = Branch top p0 p1

data ZDDCase2Node
  = ZDDCase2LT Int Node Node
  | ZDDCase2GT Int Node Node
  | ZDDCase2EQ Int Node Node Node Node

zddCase2Node :: forall a. ItemOrder a => Proxy a -> Node -> Node -> ZDDCase2Node
zddCase2Node _ (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compareItem (Proxy :: Proxy a) ptop qtop of
    LT -> ZDDCase2LT ptop p0 p1
    GT -> ZDDCase2GT qtop q0 q1
    EQ -> ZDDCase2EQ ptop q0 q1 q0 q1
zddCase2Node _ (Branch ptop p0 p1) _ = ZDDCase2LT ptop p0 p1
zddCase2Node _ _ (Branch qtop q0 q1) = ZDDCase2GT qtop q0 q1
zddCase2Node _ _ _ = error "should not happen"

-- | The empty set (∅).
zddEmpty :: ZDD a
zddEmpty = ZDD F

-- | The set containing only the empty set ({∅}).
zddUnit :: ZDD a
zddUnit = ZDD T

-- | Subsets that contain a particular element
zddSubset1 :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
zddSubset1 var (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f T = return F
      f F = return F
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return F
              EQ -> return p1
              LT -> liftM2 (zddNode top) (f p0) (f p1)
            H.insert h p ret
            return ret
  ret <- f node
  return (ZDD ret)

-- | Subsets that does not contain a particular element
zddSubset0 :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
zddSubset0 var (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f p@T = return p
      f F = return F
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return p
              EQ -> return p0
              LT -> liftM2 (zddNode top) (f p0) (f p1)
            H.insert h p ret
            return ret
  ret <- f node
  return (ZDD ret)

-- | @zddChange x p@ returns {if x∈s then s∖{x} else s∪{x} | s∈P}
zddChange :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
zddChange var (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f p@T = return p
      f F = return F
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return (zddNode var F p)
              EQ -> return (zddNode var p1 p0)
              LT -> liftM2 (zddNode top) (f p0) (f p1)
            H.insert h p ret
            return ret
  ret <- f node
  return (ZDD ret)

-- | Union of two family of sets.
zddUnion :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
zddUnion (ZDD node1) (ZDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f F q = return q
      f p F = return p
      f p q | p == q = return p
      f p q = do
        m <- H.lookup h (p, q)
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2Node (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (zddNode ptop) (f p0 q) (pure p1)
              ZDDCase2GT qtop q0 q1 -> liftM2 (zddNode qtop) (f p q0) (pure q1)
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (zddNode top) (f p0 q0) (f p1 q1)
            H.insert h (p, q) ret
            return ret
  ret <- f node1 node2
  return (ZDD ret)

-- | Intersection of two family of sets.
zddIntersection :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
zddIntersection (ZDD node1) (ZDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f F _q = return F
      f _p F = return F
      f p q | p == q = return p
      f p q = do
        m <- H.lookup h (p, q)
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2Node (Proxy :: Proxy a) p q of
              ZDDCase2LT _ptop p0 _p1 -> f p0 q
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (zddNode top) (f p0 q0) (f p1 q1)
            H.insert h (p, q) ret
            return ret
  ret <- f node1 node2
  return (ZDD ret)

-- | Difference of two family of sets.
zddDifference :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
zddDifference (ZDD node1) (ZDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f F _ = return F
      f p F = return p
      f p q | p == q = return F
      f p q = do
        m <- H.lookup h (p, q)
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2Node (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (zddNode ptop) (f p0 q) (pure p1)
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (zddNode top) (f p0 q0) (f p1 q1)
            H.insert h (p, q) ret
            return ret
  ret <- f node1 node2
  return (ZDD ret)

{-# SPECIALIZE zddSize :: ZDD a -> Int #-}
{-# SPECIALIZE zddSize :: ZDD a -> Integer #-}
{-# SPECIALIZE zddSize :: ZDD a -> Natural #-}
-- | The number of sets in the family.
zddSize :: (Integral b) => ZDD a -> b
zddSize (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return 0
      f T = return 1
      f p@(Branch _ p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- liftM2 (+) (f p0) (f p1)
            H.insert h p ret
            return ret
  f node

-- | Convert the family to a set of 'IntSet'.
zddToSetOfIntSets :: ZDD a -> Set IntSet
zddToSetOfIntSets (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return Set.empty
      f T = return (Set.singleton IntSet.empty)
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- liftM2 Set.union (f p0) (liftM (Set.map (IntSet.insert top)) (f p1))
            H.insert h p ret
            return ret
  f node

-- ------------------------------------------------------------------------
