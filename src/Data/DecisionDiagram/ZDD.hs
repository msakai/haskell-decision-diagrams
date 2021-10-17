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
  , unit

  -- * Combine
  , union
  , intersection
  , difference

  -- * Update
  , change

  -- * Query
  , subset1
  , subset0
  , size

  -- * Conversion
  , toSetOfIntSets
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
empty :: ZDD a
empty = ZDD F

-- | The set containing only the empty set ({∅}).
unit :: ZDD a
unit = ZDD T

-- | Subsets that contain a particular element
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
union :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
union (ZDD node1) (ZDD node2) = runST $ do
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
intersection :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
intersection (ZDD node1) (ZDD node2) = runST $ do
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
