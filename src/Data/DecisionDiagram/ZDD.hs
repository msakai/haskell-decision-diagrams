{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
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
    ZDD (ZDD, Empty, Base, Branch)

  -- * Item ordering
  , ItemOrder (..)
  , DefaultOrder
  , withDefaultOrder
  , withCustomOrder

  -- * Construction
  , empty
  , base
  , singleton
  , fromListOfIntSets
  , fromSetOfIntSets

  -- * Insertion
  , insert

  -- * Deletion
  , delete

  -- * Query
  , member
  , notMember
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

  -- * Map
  , mapInsert
  , mapDelete
  , change

  -- * Fold
  , fold
  , fold'

  -- * Minimal hitting sets
  , minimalHittingSets
  , minimalHittingSetsToda
  , minimalHittingSetsKnuth
  , minimalHittingSetsImai

  -- * Random sampling
  , uniformM

  -- * Min/Max
  , findMinSum
  , findMaxSum

  -- * Misc
  , flatten

  -- * Conversion
  , toListOfIntSets
  , toSetOfIntSets

  -- ** Conversion from/to graphs
  , Graph
  , Node (..)
  , toGraph
  , toGraph'
  , fromGraph
  , fromGraph'
  ) where

import Prelude hiding (null)

import Control.Monad
#if !MIN_VERSION_mwc_random(0,15,0)
import Control.Monad.Primitive
#endif
import Control.Monad.ST
import qualified Data.Foldable as Foldable
import Data.Functor.Identity
import Data.Hashable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortBy)
import Data.Maybe
import Data.Proxy
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import qualified GHC.Exts as Exts
import Numeric.Natural
#if MIN_VERSION_mwc_random(0,15,0)
import System.Random.Stateful (StatefulGen (..))
#else
import System.Random.MWC (Gen)
#endif
import System.Random.MWC.Distributions (bernoulli)
import Text.Read

import Data.DecisionDiagram.BDD.Internal.ItemOrder
import qualified Data.DecisionDiagram.BDD.Internal.Node as Node
import qualified Data.DecisionDiagram.BDD as BDD

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Zero-suppressed binary decision diagram representing family of sets
newtype ZDD a = ZDD Node.Node
  deriving (Eq, Hashable)

pattern Empty :: ZDD a
pattern Empty = ZDD Node.F

pattern Base :: ZDD a
pattern Base = ZDD Node.T

-- | Smart constructor that takes the ZDD reduction rules into account
pattern Branch :: Int -> ZDD a -> ZDD a -> ZDD a
pattern Branch x lo hi <- ZDD (Node.Branch x (ZDD -> lo) (ZDD -> hi)) where
  Branch _ p0 Empty = p0
  Branch x (ZDD lo) (ZDD hi) = ZDD (Node.Branch x lo hi)

{-# COMPLETE Empty, Base, Branch #-}

nodeId :: ZDD a -> Int
nodeId (ZDD node) = Node.nodeId node

-- ------------------------------------------------------------------------

instance Show (ZDD a) where
  showsPrec d a   = showParen (d > 10) $
    showString "fromGraph " . shows (toGraph a)

instance Read (ZDD a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromGraph" <- lexP
    gv <- readPrec
    return (fromGraph gv)

  readListPrec = readListPrecDefault

instance ItemOrder a => Exts.IsList (ZDD a) where
  type Item (ZDD a) = IntSet

  fromList = fromListOfSortedList . map f
    where
      f :: IntSet -> [Int]
      f = sortBy (compareItem (Proxy :: Proxy a)) . IntSet.toList

  toList = fold' [] [IntSet.empty] (\top lo hi -> lo <> map (IntSet.insert top) hi)

-- ------------------------------------------------------------------------

data ZDDCase2 a
  = ZDDCase2LT Int (ZDD a) (ZDD a)
  | ZDDCase2GT Int (ZDD a) (ZDD a)
  | ZDDCase2EQ Int (ZDD a) (ZDD a) (ZDD a) (ZDD a)

zddCase2 :: forall a. ItemOrder a => Proxy a -> ZDD a -> ZDD a -> ZDDCase2 a
zddCase2 _ (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compareItem (Proxy :: Proxy a) ptop qtop of
    LT -> ZDDCase2LT ptop p0 p1
    GT -> ZDDCase2GT qtop q0 q1
    EQ -> ZDDCase2EQ ptop p0 p1 q0 q1
zddCase2 _ (Branch ptop p0 p1) _ = ZDDCase2LT ptop p0 p1
zddCase2 _ _ (Branch qtop q0 q1) = ZDDCase2GT qtop q0 q1
zddCase2 _ _ _ = error "should not happen"

-- | The empty set (∅).
empty :: ZDD a
empty = Empty

-- | The set containing only the empty set ({∅}).
base :: ZDD a
base = Base

-- | Create a ZDD that contains only a given set.
singleton :: forall a. ItemOrder a => IntSet -> ZDD a
singleton xs = insert xs empty

-- | Select subsets that contain a particular element and then remove the element from them
subset1 :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
subset1 var zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f Base = return Empty
      f Empty = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return Empty
              EQ -> return p1
              LT -> liftM2 (Branch top) (f p0) (f p1)
            H.insert h p ret
            return ret
  f zdd

-- | Subsets that does not contain a particular element
subset0 :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
subset0 var zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f p@Base = return p
      f Empty = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return p
              EQ -> return p0
              LT -> liftM2 (Branch top) (f p0) (f p1)
            H.insert h p ret
            return ret
  f zdd

-- | Insert a set into the ZDD.
insert :: forall a. ItemOrder a => IntSet -> ZDD a -> ZDD a
insert xs = f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs))
  where
    f [] Empty = Base
    f [] Base = Base
    f [] (Branch top p0 p1) = Branch top (f [] p0) p1
    f (y : ys) Empty = Branch y Empty (f ys Empty)
    f (y : ys) Base = Branch y Base (f ys Empty)
    f yys@(y : ys) p@(Branch top p0 p1) =
      case compareItem (Proxy :: Proxy a) y top of
        LT -> Branch y p (f ys Empty)
        GT -> Branch top (f yys p0) p1
        EQ -> Branch top p0 (f ys p1)

-- | Delete a set from the ZDD.
delete :: forall a. ItemOrder a => IntSet -> ZDD a -> ZDD a
delete xs = f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs))
  where
    f [] Empty = Empty
    f [] Base = Empty
    f [] (Branch top p0 p1) = Branch top (f [] p0) p1
    f (_ : _) Empty = Empty
    f (_ : _) Base = Base
    f yys@(y : ys) p@(Branch top p0 p1) =
      case compareItem (Proxy :: Proxy a) y top of
        LT -> p
        GT -> Branch top (f yys p0) p1
        EQ -> Branch top p0 (f ys p1)

-- | Insert an item into each element set of ZDD.
mapInsert :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
mapInsert var zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f p@Base = return (Branch var Empty p)
      f Empty = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return (Branch var Empty p)
              LT -> liftM2 (Branch top) (f p0) (f p1)
              EQ -> return (Branch top Empty (p0 `union` p1))
            H.insert h p ret
            return ret
  f zdd

-- | Delete an item from each element set of ZDD.
mapDelete :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
mapDelete var zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f Base = return Base
      f Empty = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return p
              LT -> liftM2 (Branch top) (f p0) (f p1)
              EQ -> return (p0 `union` p1)
            H.insert h p ret
            return ret
  f zdd

-- | @change x p@ returns {if x∈s then s∖{x} else s∪{x} | s∈P}
change :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
change var zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f p@Base = return (Branch var Empty p)
      f Empty = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return (Branch var Empty p)
              EQ -> return (Branch var p1 p0)
              LT -> liftM2 (Branch top) (f p0) (f p1)
            H.insert h p ret
            return ret
  f zdd

-- | Union of two family of sets.
union :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
union zdd1 zdd2 = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty q = return q
      f p Empty = return p
      f p q | p == q = return p
      f p q = do
        let key = if nodeId p <= nodeId q then (p, q) else (q, p)
        m <- H.lookup h key
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2 (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (Branch ptop) (f p0 q) (pure p1)
              ZDDCase2GT qtop q0 q1 -> liftM2 (Branch qtop) (f p q0) (pure q1)
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (Branch top) (f p0 q0) (f p1 q1)
            H.insert h key ret
            return ret
  f zdd1 zdd2

-- | Unions of a list of ZDDs.
unions :: forall f a. (Foldable f, ItemOrder a) => f (ZDD a) -> ZDD a
unions xs = Foldable.foldl' union empty xs

-- | Intersection of two family of sets.
intersection :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
intersection zdd1 zdd2 = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty _q = return Empty
      f _p Empty = return Empty
      f p q | p == q = return p
      f p q = do
        let key = if nodeId p <= nodeId q then (p, q) else (q, p)
        m <- H.lookup h key
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2 (Proxy :: Proxy a) p q of
              ZDDCase2LT _ptop p0 _p1 -> f p0 q
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (Branch top) (f p0 q0) (f p1 q1)
            H.insert h key ret
            return ret
  f zdd1 zdd2

-- | Difference of two family of sets.
difference :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
difference zdd1 zdd2 = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty _ = return Empty
      f p Empty = return p
      f p q | p == q = return Empty
      f p q = do
        m <- H.lookup h (p, q)
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2 (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (Branch ptop) (f p0 q) (pure p1)
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> liftM2 (Branch top) (f p0 q0) (f p1 q1)
            H.insert h (p, q) ret
            return ret
  f zdd1 zdd2

-- | See 'difference'
(\\) :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
m1 \\ m2 = difference m1 m2

-- | Given a family P and Q, it computes {S∈P | ∀X∈Q. X⊈S}
--
-- Sometimes it is denoted as /P ↘ Q/.
nonSuperset :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
nonSuperset zdd1 zdd2 = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty _ = return Empty
      f _ Base = return Empty
      f p Empty = return p
      f p q | p == q = return Empty
      f p q = do
        m <- H.lookup h (p, q)
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case zddCase2 (Proxy :: Proxy a) p q of
              ZDDCase2LT ptop p0 p1 -> liftM2 (Branch ptop) (f p0 q) (f p1 q)
              ZDDCase2GT _qtop q0 _q1 -> f p q0
              ZDDCase2EQ top p0 p1 q0 q1 -> do
                r <- liftM2 intersection (f p1 q0) (f p1 q1)
                liftM2 (Branch top) (f p0 q0) (pure r)
            H.insert h (p, q) ret
            return ret
  f zdd1 zdd2

minimalHittingSetsKnuth' :: forall a. ItemOrder a => Bool -> ZDD a -> ZDD a
minimalHittingSetsKnuth' imai zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty = return Base
      f Base = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            -- TODO: memoize union and difference/nonSuperset?
            r0 <- f (union p0 p1)
            r1 <- liftM2 (if imai then difference else nonSuperset) (f p0) (pure r0)
            let ret = Branch top r0 r1
            H.insert h p ret
            return ret
  f zdd

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
hittingSetsBDD = fold' BDD.true BDD.false (\top h0 h1 -> h0 BDD..&&. BDD.Branch top h1 BDD.true)

minimal :: forall a. ItemOrder a => BDD.BDD a -> ZDD a
minimal bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f BDD.F = return Empty
      f BDD.T = return Base
      f p@(BDD.Branch x lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ml <- f lo
            mh <- f hi
            let ret = Branch x ml (difference mh ml)
            H.insert h p ret
            return ret
  f bdd

-- | See 'minimalHittingSetsToda'.
minimalHittingSets :: forall a. ItemOrder a => ZDD a -> ZDD a
minimalHittingSets = minimalHittingSetsToda

-- | Is the set a member of the family?
member :: forall a. (ItemOrder a) => IntSet -> ZDD a -> Bool
member xs = member' xs'
  where
    xs' = sortBy (compareItem (Proxy :: Proxy a)) $ IntSet.toList xs

member' :: forall a. (ItemOrder a) => [Int] -> ZDD a -> Bool
member' [] Base = True
member' [] (Branch _ p0 _) = member' [] p0
member' yys@(y:ys) (Branch top p0 p1) =
  case compareItem (Proxy :: Proxy a) y top of
    EQ -> member' ys p1
    GT -> member' yys p0
    LT -> False
member' _ _ = False

-- | Is the set not in the family?
notMember :: forall a. (ItemOrder a) => IntSet -> ZDD a -> Bool
notMember xs = not . member xs

-- | Is this the empty set?
null :: ZDD a -> Bool
null = (empty ==)

{-# SPECIALIZE size :: ZDD a -> Int #-}
{-# SPECIALIZE size :: ZDD a -> Integer #-}
{-# SPECIALIZE size :: ZDD a -> Natural #-}
-- | The number of sets in the family.
size :: (Integral b) => ZDD a -> b
size = fold' 0 1 (\_ n0 n1 -> n0 + n1)

-- | @(s1 `isSubsetOf` s2)@ indicates whether @s1@ is a subset of @s2@.
isSubsetOf :: ItemOrder a => ZDD a -> ZDD a -> Bool
isSubsetOf a b = union a b == b

-- | @(s1 `isProperSubsetOf` s2)@ indicates whether @s1@ is a proper subset of @s2@.
isProperSubsetOf :: ItemOrder a => ZDD a -> ZDD a -> Bool
isProperSubsetOf a b = a `isSubsetOf` b && a /= b

-- | Check whether two sets are disjoint (i.e., their intersection is empty).
disjoint :: ItemOrder a => ZDD a -> ZDD a -> Bool
disjoint a b = null (a `intersection` b)

--- | Unions of all member sets
flatten :: ItemOrder a => ZDD a -> IntSet
flatten = fold' IntSet.empty IntSet.empty (\top lo hi -> IntSet.insert top (lo `IntSet.union` hi))

-- | Create a ZDD from a set of 'IntSet'
fromSetOfIntSets :: forall a. ItemOrder a => Set IntSet -> ZDD a
fromSetOfIntSets = fromListOfIntSets . Set.toList

-- | Convert the family to a set of 'IntSet'.
toSetOfIntSets :: ZDD a -> Set IntSet
toSetOfIntSets = fold' Set.empty (Set.singleton IntSet.empty) (\top lo hi -> lo <> Set.map (IntSet.insert top) hi)

-- | Create a ZDD from a list of 'IntSet'
fromListOfIntSets :: forall a. ItemOrder a => [IntSet] -> ZDD a
fromListOfIntSets = fromListOfSortedList . map f
  where
    f :: IntSet -> [Int]
    f = sortBy (compareItem (Proxy :: Proxy a)) . IntSet.toList

-- | Convert the family to a list of 'IntSet'.
toListOfIntSets :: ZDD a -> [IntSet]
toListOfIntSets = fold [] [IntSet.empty] (\top lo hi -> lo <> map (IntSet.insert top) hi)

fromListOfSortedList :: forall a. ItemOrder a => [[Int]] -> ZDD a
fromListOfSortedList = unions . map f
  where
    f :: [Int] -> ZDD a
    f = foldr (\x node -> Branch x Empty node) Base

-- | Fold over the graph structure of the ZDD.
--
-- It takes values for substituting 'empty' and 'base',
-- and a function for substiting non-terminal node.
fold :: b -> b -> (Int -> b -> b -> b) -> ZDD a -> b
fold ff tt br zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty = return ff
      f Base = return tt
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f p0
            r1 <- f p1
            let ret = br top r0 r1
            H.insert h p ret
            return ret
  f zdd

-- | Strict version of 'fold'
fold' :: b -> b -> (Int -> b -> b -> b) -> ZDD a -> b
fold' !ff !tt br zdd = runST $ do
  h <- C.newSized defaultTableSize
  let f Empty = return ff
      f Base = return tt
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f p0
            r1 <- f p1
            let ret = br top r0 r1
            seq ret $ H.insert h p ret
            return ret
  f zdd

-- ------------------------------------------------------------------------

-- | Sample a set from uniform distribution over elements of the ZDD.
--
-- The function constructs a table internally and the table is shared across
-- multiple use of the resulting action (@m IntSet@).
-- Therefore, the code
--
-- @
-- let g = uniformM zdd gen
-- s1 <- g
-- s2 <- g
-- @
--
-- is more efficient than
--
-- @
-- s1 <- uniformM zdd gen
-- s2 <- uniformM zdd gen
-- @
-- .
#if MIN_VERSION_mwc_random(0,15,0)
uniformM :: forall a g m. (ItemOrder a, StatefulGen g m) => ZDD a -> g -> m IntSet
#else
uniformM :: forall a m. (ItemOrder a, PrimMonad m) => ZDD a -> Gen (PrimState m) -> m IntSet
#endif
uniformM Empty = error "Data.DecisionDiagram.ZDD.uniformM: empty ZDD"
uniformM zdd = func
  where
    func gen = f zdd []
      where
        f Empty _ = error "Data.DecisionDiagram.ZDD.uniformM: should not happen"
        f Base r = return $ IntSet.fromList r
        f p@(Branch top p0 p1) r = do
          b <- bernoulli (table HashMap.! p) gen
          if b then
            f p1 (top : r)
          else
            f p0 r

    table :: HashMap (ZDD a) Double
    table = runST $ do
      h <- C.newSized defaultTableSize
      let f Empty = return (0 :: Integer)
          f Base = return 1
          f p@(Branch _ p0 p1) = do
            m <- H.lookup h p
            case m of
              Just (ret, _) -> return ret
              Nothing -> do
                n0 <- f p0
                n1 <- f p1
                let s = n0 + n1
                    r :: Double
                    r = realToFrac (n1 % (n0 + n1))
                seq r $ H.insert h p (s, r)
                return s
      _ <- f zdd
      xs <- H.toList h
      return $ HashMap.fromList [(n, r) | (n, (_, r)) <- xs]

-- ------------------------------------------------------------------------

-- | Find a minimum element set with respect to given weight function
--
-- \[
-- \min_{X\in S} \sum_{x\in X} w(x)
-- \]
findMinSum :: forall a w. (ItemOrder a, Num w, Ord w) => (Int -> w) -> ZDD a -> (w, IntSet)
findMinSum weight =
  fromMaybe (error "Data.DecisionDiagram.ZDD.findMinSum: empty ZDD") .
    fold' Nothing (Just (0, IntSet.empty)) f
  where
    f _ _ Nothing = undefined
    f x z1 (Just (w2, s2)) =
      case z1 of
        Just (w1, _) | w1 <= w2' -> z1
        _ -> seq w2' $ seq s2' $ Just (w2', s2')
      where
        w2' = w2 + weight x
        s2' = IntSet.insert x s2

-- | Find a maximum element set with respect to given weight function
--
-- \[
-- \max_{X\in S} \sum_{x\in X} w(x)
-- \]
findMaxSum :: forall a w. (ItemOrder a, Num w, Ord w) => (Int -> w) -> ZDD a -> (w, IntSet)
findMaxSum weight =
  fromMaybe (error "Data.DecisionDiagram.ZDD.findMinSum: empty ZDD") .
    fold' Nothing (Just (0, IntSet.empty)) f
  where
    f _ _ Nothing = undefined
    f x z1 (Just (w2, s2)) =
      case z1 of
        Just (w1, _) | w1 >= w2' -> z1
        _ -> seq w2' $ seq s2' $ Just (w2', s2')
      where
        w2' = w2 + weight x
        s2' = IntSet.insert x s2

-- ------------------------------------------------------------------------

type Graph = IntMap Node

data Node
  = NodeEmpty
  | NodeBase
  | NodeBranch !Int Int Int
  deriving (Eq, Show, Read)

-- | Convert a ZDD into a pointed graph
toGraph :: ZDD a -> (Graph, Int)
toGraph bdd =
  case toGraph' (Identity bdd) of
    (g, Identity v) -> (g, v)

-- | Convert multiple ZDDs into a graph
toGraph' :: Traversable t => t (ZDD a) -> (Graph, t Int)
toGraph' bs = runST $ do
  h <- C.newSized defaultTableSize
  H.insert h Empty 0
  H.insert h Base 1
  counter <- newSTRef 2
  ref <- newSTRef $ IntMap.fromList [(0, NodeEmpty), (1, NodeBase)]

  let f Empty = return 0
      f Base = return 1
      f p@(Branch x lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f lo
            r1 <- f hi
            n <- readSTRef counter
            writeSTRef counter $! n+1
            H.insert h p n
            modifySTRef' ref (IntMap.insert n (NodeBranch x r0 r1))
            return n

  vs <- mapM f bs
  g <- readSTRef ref
  return (g, vs)

-- | Convert a pointed graph into a ZDD
fromGraph :: (Graph, Int) -> ZDD a
fromGraph (g, v) =
  case IntMap.lookup v (fromGraph' g) of
    Nothing -> error ("Data.DecisionDiagram.ZDD.fromGraph: invalid node id " ++ show v)
    Just bdd -> bdd

-- | Convert nodes of a graph into ZDDs
fromGraph' :: Graph -> IntMap (ZDD a)
fromGraph' g = ret
  where
    ret = IntMap.map f g
    f NodeEmpty = Empty
    f NodeBase = Base
    f (NodeBranch x lo hi) =
      case (IntMap.lookup lo ret, IntMap.lookup hi ret) of
        (Nothing, _) -> error ("Data.DecisionDiagram.ZDD.fromGraph': invalid node id " ++ show lo)
        (_, Nothing) -> error ("Data.DecisionDiagram.ZDD.fromGraph': invalid node id " ++ show hi)
        (Just lo', Just hi') -> Branch x lo' hi'

-- ------------------------------------------------------------------------
