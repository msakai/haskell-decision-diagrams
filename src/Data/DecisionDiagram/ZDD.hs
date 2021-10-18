{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.DecisionDiagram.ZDD
-- Copyright   :  (c) Masahiro Sakai 2021
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
--
-- Zero-Suppressed binary decision diagram.
--
-- References:
--
-- * S. Minato, "Zero-Suppressed BDDs for Set Manipulation in Combinatorial Problems,"
--   30th ACM/IEEE Design Automation Conference, 1993, pp. 272-277,
--   doi: [10.1145/157485.164890](https://doi.org/10.1145/157485.164890).
--   <https://www.researchgate.net/publication/221062015_Zero-Suppressed_BDDs_for_Set_Manipulation_in_Combinatorial_Problems>
--
----------------------------------------------------------------------
module Data.DecisionDiagram.ZDD
  (
  -- * ZDD type
    ZDD (..)

  -- * Item ordering
  , ItemOrder (..)
  , DefaultOrder
  , withDefaultOrder
  , withCustomOrder

  -- * Construction
  , empty
  , base
  , fromSetOfIntSets

  -- * Query
  , null
  , size
  , isSubsetOf
  , isProperSubsetOf
  , disjoint

  -- * Combine
  , union
  , unions
  , intersection
  , difference
  , (\\)
  , nonSuperset

  -- * Filter
  , subset1
  , subset0

  -- * Update
  , change

  -- * Minimal hitting sets
  , minimalHittingSets
  , minimalHittingSetsToda
  , minimalHittingSetsKnuth
  , minimalHittingSetsImai

  -- * Conversion
  , toSetOfIntSets
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.ST
import qualified Data.Foldable as Foldable
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortBy)
import Data.Proxy
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric.Natural

import Data.DecisionDiagram.BDD.Internal
import qualified Data.DecisionDiagram.BDD as BDD

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Zero-suppressed binary decision diagram representing family of sets
newtype ZDD a = ZDD Node
  deriving (Eq, Hashable, Show)

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
    EQ -> ZDDCase2EQ ptop p0 p1 q0 q1
zddCase2Node _ (Branch ptop p0 p1) _ = ZDDCase2LT ptop p0 p1
zddCase2Node _ _ (Branch qtop q0 q1) = ZDDCase2GT qtop q0 q1
zddCase2Node _ _ _ = error "should not happen"

-- | The empty set (∅).
empty :: ZDD a
empty = ZDD F

-- | The set containing only the empty set ({∅}).
base :: ZDD a
base = ZDD T

-- | Select subsets that contain a particular element and then remove the element from them
subset1 :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
subset1 var (ZDD node) = runST $ do
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
subset0 :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
subset0 var (ZDD node) = runST $ do
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

-- | @change x p@ returns {if x∈s then s∖{x} else s∪{x} | s∈P}
change :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
change var (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f p@T = return (zddNode var F p)
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
union :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
union (ZDD node1) (ZDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f F q = return q
      f p F = return p
      f p q | p == q = return p
      f p q = do
        let key = if nodeId p <= nodeId q then (p, q) else (q, p)
        m <- H.lookup h key
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2Node (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (zddNode ptop) (f p0 q) (pure p1)
              ZDDCase2GT qtop q0 q1 -> liftM2 (zddNode qtop) (f p q0) (pure q1)
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (zddNode top) (f p0 q0) (f p1 q1)
            H.insert h key ret
            return ret
  ret <- f node1 node2
  return (ZDD ret)

-- | Unions of a list of ZDDs.
unions :: forall f a. (Foldable f, ItemOrder a) => f (ZDD a) -> ZDD a
unions xs = Foldable.foldl' union empty xs

-- | Intersection of two family of sets.
intersection :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
intersection (ZDD node1) (ZDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f F _q = return F
      f _p F = return F
      f p q | p == q = return p
      f p q = do
        let key = if nodeId p <= nodeId q then (p, q) else (q, p)
        m <- H.lookup h key
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2Node (Proxy :: Proxy a) p q of
              ZDDCase2LT _ptop p0 _p1 -> f p0 q
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (zddNode top) (f p0 q0) (f p1 q1)
            H.insert h key ret
            return ret
  ret <- f node1 node2
  return (ZDD ret)

-- | Difference of two family of sets.
difference :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
difference (ZDD node1) (ZDD node2) = runST $ do
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

-- | See 'difference'
(\\) :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
m1 \\ m2 = difference m1 m2

-- | Given a family P and Q, it computes {S∈P | ∀X∈Q. X⊈S}
--
-- Sometimes it is denoted as /P ↘ Q/.
nonSuperset :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
nonSuperset (ZDD node1) (ZDD node2) = runST $ do
  h <- C.newSized defaultTableSize
  let f F _ = return F
      f _ T = return F
      f p F = return p
      f p q | p == q = return F
      f p q = do
        m <- H.lookup h (p, q)
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2Node (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (zddNode ptop) (f p0 q) (f p1 q)
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> do
                n0 <- f p1 q0
                n1 <- f p1 q1
                let ZDD r = intersection (ZDD n0 :: ZDD a) (ZDD n1) -- TODO: memoize intersection?
                liftM2 (zddNode top) (f p0 q0) (pure r)
            H.insert h (p, q) ret
            return ret
  ret <- f node1 node2
  return (ZDD ret)

minimalHittingSetsKnuth' :: forall a. ItemOrder a => Bool -> ZDD a -> ZDD a
minimalHittingSetsKnuth' imai (ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return T
      f T = return F
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            -- TODO: memoize union and difference/nonSuperset?
            r0 <- case union (ZDD p0) (ZDD p1) :: ZDD a of
                    ZDD r -> f r
            ZDD r1 <- liftM2 (if imai then difference else nonSuperset) (liftM ZDD (f p0)) (pure (ZDD r0 :: ZDD a))
            let ret = zddNode top r0 r1
            H.insert h p ret
            return ret
  ret <- f node
  return (ZDD ret)

-- | Minimal hitting sets.
--
-- D. E. Knuth, "The Art of Computer Programming, Volume 4A:
-- Combinatorial Algorithms, Part 1," Addison-Wesley Professional,
-- 2011.
minimalHittingSetsKnuth :: forall a. ItemOrder a => ZDD a -> ZDD a
minimalHittingSetsKnuth = minimalHittingSetsKnuth' False

-- | Minimal hitting sets.
--
-- T. Imai, "One-line hack of knuth's algorithm for minimal hitting set
-- computation with ZDDs," vol. 2015-AL-155, no. 15, Nov. 2015, pp. 1-3.
-- [Online]. Available: <http://id.nii.ac.jp/1001/00145799/>.
minimalHittingSetsImai :: forall a. ItemOrder a => ZDD a -> ZDD a
minimalHittingSetsImai = minimalHittingSetsKnuth' True

-- | Minimal hitting sets.
--
-- * T. Toda, “Hypergraph Transversal Computation with Binary Decision Diagrams,”
--   SEA 2013: Experimental Algorithms.
--   Available: <http://dx.doi.org/10.1007/978-3-642-38527-8_10>.
--
-- * HTC-BDD: Hypergraph Transversal Computation with Binary Decision Diagrams
--   <https://www.disc.lab.uec.ac.jp/toda/htcbdd.html>
minimalHittingSetsToda :: forall a. ItemOrder a => ZDD a -> ZDD a
minimalHittingSetsToda = minimal . hittingSetsBDD

hittingSetsBDD :: forall a. ItemOrder a => ZDD a -> BDD.BDD a
hittingSetsBDD(ZDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return BDD.true
      f T = return BDD.false
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            BDD.BDD h0 <- f p0
            BDD.BDD h1 <- f p1
            let ret = BDD.BDD h0 BDD..&&. BDD.BDD (bddNode top h1 T)
            H.insert h p ret
            return ret
  ret <- f node
  return ret
  where
    -- XXX
    bddNode :: Int -> Node -> Node -> Node
    bddNode ind lo hi
      | lo == hi = lo
      | otherwise = Branch ind lo hi

minimal :: forall a. ItemOrder a => BDD.BDD a -> ZDD a
minimal (BDD.BDD node) = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return F
      f T = return T
      f p@(Branch x lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ml <- f lo
            mh <- f hi
            let ZDD t = difference (ZDD mh :: ZDD a) (ZDD ml)
                ret = zddNode x ml t
            H.insert h p ret
            return ret
  ret <- f node
  return (ZDD ret)

-- | See 'minimalHittingSetsToda'.
minimalHittingSets :: forall a. ItemOrder a => ZDD a -> ZDD a
minimalHittingSets = minimalHittingSetsToda

-- | Is this the empty set?
null :: ZDD a -> Bool
null = (empty ==)

{-# SPECIALIZE size :: ZDD a -> Int #-}
{-# SPECIALIZE size :: ZDD a -> Integer #-}
{-# SPECIALIZE size :: ZDD a -> Natural #-}
-- | The number of sets in the family.
size :: (Integral b) => ZDD a -> b
size (ZDD node) = runST $ do
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

-- | Is this the empty set?
isSubsetOf :: ItemOrder a => ZDD a -> ZDD a -> Bool
isSubsetOf a b = union a b == b

-- | @(s1 `isProperSubsetOf` s2)@ indicates whether @s1@ is a proper subset of @s2@.
isProperSubsetOf :: ItemOrder a => ZDD a -> ZDD a -> Bool
isProperSubsetOf a b = a `isSubsetOf` b && a /= b

-- | Check whether two sets are disjoint (i.e., their intersection is empty).
disjoint :: ItemOrder a => ZDD a -> ZDD a -> Bool
disjoint a b = null (a `intersection` b)

-- | Create a ZDD from a set of 'IntSet'
fromSetOfIntSets :: forall a. ItemOrder a => Set IntSet -> ZDD a
fromSetOfIntSets xss = unions
  [ ZDD $ foldr (\x node -> Branch x F node) T
        $ sortBy (compareItem (Proxy :: Proxy a))
        $ IntSet.toList xs
  | xs <- Set.toList xss
  ]    

-- | Convert the family to a set of 'IntSet'.
toSetOfIntSets :: ZDD a -> Set IntSet
toSetOfIntSets (ZDD node) = runST $ do
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
