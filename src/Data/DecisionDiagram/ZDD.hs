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
    ZDD (Leaf, Branch)
  , pattern Empty
  , pattern Base

  -- * Item ordering
  , ItemOrder (..)
  , AscOrder
  , DescOrder
  , withDefaultOrder
  , withAscOrder
  , withDescOrder
  , withCustomOrder

  -- * Construction
  , empty
  , base
  , singleton
  , subsets
  , combinations
  , fromListOfIntSets
  , fromSetOfIntSets

  -- ** Pseudo-boolean constraints
  , subsetsAtLeast
  , subsetsAtMost
  , subsetsExactly
  , subsetsExactlyIntegral

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
  , numNodes

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

  -- * (Co)algebraic structure
  , Sig (..)
  , pattern SEmpty
  , pattern SBase
  , inSig
  , outSig

  -- * Fold
  , fold
  , fold'

  -- * Unfold
  , unfoldHashable
  , unfoldOrd

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
import Data.Function (on)
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
import Data.List (foldl', sortBy)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Data.Proxy
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import qualified Data.Vector as V
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
import Data.DecisionDiagram.BDD.Internal.Node (Sig (..))
import qualified Data.DecisionDiagram.BDD.Internal.Node as Node
import qualified Data.DecisionDiagram.BDD as BDD

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Zero-suppressed binary decision diagram representing family of sets
newtype ZDD a = ZDD Node.Node
  deriving (Eq, Hashable)

-- | Synonym of @'Leaf' False@
pattern Empty :: ZDD a
pattern Empty = Leaf False

-- | Synonym of @'Leaf' True@
pattern Base :: ZDD a
pattern Base = Leaf True

pattern Leaf :: Bool -> ZDD a
pattern Leaf b = ZDD (Node.Leaf b)

-- | Smart constructor that takes the ZDD reduction rules into account
pattern Branch :: Int -> ZDD a -> ZDD a -> ZDD a
pattern Branch x lo hi <- ZDD (Node.Branch x (ZDD -> lo) (ZDD -> hi)) where
  Branch _ p0 Empty = p0
  Branch x (ZDD lo) (ZDD hi) = ZDD (Node.Branch x lo hi)

{-# COMPLETE Empty, Base, Branch #-}
{-# COMPLETE Leaf, Branch #-}

-- Hack for avoiding spurious incomplete patterns warning on the above Branch pattern definition.
#if __GLASGOW_HASKELL__ < 810
{-# COMPLETE ZDD #-}
#endif

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

  toList = toListOfIntSets

-- ------------------------------------------------------------------------

data ZDDCase2 a
  = ZDDCase2LT Int (ZDD a) (ZDD a)
  | ZDDCase2GT Int (ZDD a) (ZDD a)
  | ZDDCase2EQ Int (ZDD a) (ZDD a) (ZDD a) (ZDD a)
  | ZDDCase2EQ2 Bool Bool

zddCase2 :: forall a. ItemOrder a => Proxy a -> ZDD a -> ZDD a -> ZDDCase2 a
zddCase2 _ (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compareItem (Proxy :: Proxy a) ptop qtop of
    LT -> ZDDCase2LT ptop p0 p1
    GT -> ZDDCase2GT qtop q0 q1
    EQ -> ZDDCase2EQ ptop p0 p1 q0 q1
zddCase2 _ (Branch ptop p0 p1) _ = ZDDCase2LT ptop p0 p1
zddCase2 _ _ (Branch qtop q0 q1) = ZDDCase2GT qtop q0 q1
zddCase2 _ Base Base = ZDDCase2EQ2 True True
zddCase2 _ Base Empty = ZDDCase2EQ2 True False
zddCase2 _ Empty Base = ZDDCase2EQ2 False True
zddCase2 _ Empty Empty = ZDDCase2EQ2 False False

-- | The empty set (∅).
--
-- >>> toSetOfIntSets (empty :: ZDD AscOrder)
-- fromList []
empty :: ZDD a
empty = Empty

-- | The set containing only the empty set ({∅}).
--
-- >>> toSetOfIntSets (base :: ZDD AscOrder)
-- fromList [fromList []]
base :: ZDD a
base = Base

-- | Create a ZDD that contains only a given set.
--
-- >>> toSetOfIntSets (singleton (IntSet.fromList [1,2,3]) :: ZDD AscOrder)
-- fromList [fromList [1,2,3]]
singleton :: forall a. ItemOrder a => IntSet -> ZDD a
singleton xs = insert xs empty

-- | Set of all subsets, i.e. powerset
subsets :: forall a. ItemOrder a => IntSet -> ZDD a
subsets = foldl' f Base . sortBy (flip (compareItem (Proxy :: Proxy a))) . IntSet.toList
  where
    f zdd x = Branch x zdd zdd

-- | Set of all k-combination of a set
combinations :: forall a. ItemOrder a => IntSet -> Int -> ZDD a
combinations xs k
  | k < 0 = error "Data.DecisionDiagram.ZDD.combinations: negative size"
  | otherwise = unfoldOrd f (0, k)
  where
    table = V.fromList $ sortBy (compareItem (Proxy :: Proxy a)) $ IntSet.toList xs
    n = V.length table

    f :: (Int, Int) -> Sig (Int, Int)
    f (!_, !0) = SLeaf True
    f (!i, !k')
      | i + k' > n = SLeaf False
      | otherwise  = SBranch (table V.! i) (i+1, k') (i+1, k'-1)

-- | Set of all subsets whose sum of weights is at least k.
subsetsAtLeast :: forall a w. (ItemOrder a, Real w) => IntMap w -> w -> ZDD a
subsetsAtLeast xs k0 = unfoldOrd f (0, k0)
  where
    xs' :: V.Vector (Int, w)
    xs' = V.fromList $ sortBy (compareItem (Proxy :: Proxy a) `on` fst) $ IntMap.toList xs
    ys :: V.Vector (w, w)
    ys = V.scanr (\(_, w) (lb,ub) -> if w >= 0 then (lb, ub+w) else (lb+w, ub)) (0,0) xs'

    f :: (Int, w) -> Sig (Int, w)
    f (!i, !k)
      | not (k <= ub) = SLeaf False
      | i == V.length xs' && 0 >= k = SLeaf True
      | lb >= k = SBranch x (i+1, lb) (i+1, lb) -- all remaining variables are don't-care
      | otherwise = SBranch x (i+1, k) (i+1, k-w)
      where
        (lb,ub) = ys V.! i
        (x, w) = xs' V.! i

-- | Set of all subsets whose sum of weights is at most k.
subsetsAtMost :: forall a w. (ItemOrder a, Real w) => IntMap w -> w -> ZDD a
subsetsAtMost xs k0 = unfoldOrd f (0, k0)
  where
    xs' :: V.Vector (Int, w)
    xs' = V.fromList $ sortBy (compareItem (Proxy :: Proxy a) `on` fst) $ IntMap.toList xs
    ys :: V.Vector (w, w)
    ys = V.scanr (\(_, w) (lb,ub) -> if w >= 0 then (lb, ub+w) else (lb+w, ub)) (0,0) xs'

    f :: (Int, w) -> Sig (Int, w)
    f (!i, !k)
      | not (lb <= k) = SLeaf False
      | i == V.length xs' && 0 <= k = SLeaf True
      | ub <= k = SBranch x (i+1, ub) (i+1, ub) -- all remaining variables are don't-care
      | otherwise = SBranch x (i+1, k) (i+1, k-w)
      where
        (lb,ub) = ys V.! i
        (x, w) = xs' V.! i

-- | Set of all subsets whose sum of weights is exactly k.
--
-- Note that 'combinations' is a special case where all weights are 1.
--
-- If weight type is 'Integral', 'subsetsExactlyIntegral' is more efficient.
subsetsExactly :: forall a w. (ItemOrder a, Real w) => IntMap w -> w -> ZDD a
subsetsExactly xs k0 = unfoldOrd f (0, k0)
  where
    xs' :: V.Vector (Int, w)
    xs' = V.fromList $ sortBy (compareItem (Proxy :: Proxy a) `on` fst) $ IntMap.toList xs
    ys :: V.Vector (w, w)
    ys = V.scanr (\(_, w) (lb,ub) -> if w >= 0 then (lb, ub+w) else (lb+w, ub)) (0,0) xs'

    f :: (Int, w) -> Sig (Int, w)
    f (!i, !k)
      | not (lb <= k && k <= ub) = SLeaf False
      | i == V.length xs' && 0 == k = SLeaf True
      | otherwise = SBranch x (i+1, k) (i+1, k-w)
      where
        (lb,ub) = ys V.! i
        (x, w) = xs' V.! i

-- | Similar to 'subsetsExactly' but more efficient.
subsetsExactlyIntegral :: forall a w. (ItemOrder a, Real w, Integral w) => IntMap w -> w -> ZDD a
subsetsExactlyIntegral xs k0 = unfoldOrd f (0, k0)
  where
    xs' :: V.Vector (Int, w)
    xs' = V.fromList $ sortBy (compareItem (Proxy :: Proxy a) `on` fst) $ IntMap.toList xs
    ys :: V.Vector (w, w)
    ys = V.scanr (\(_, w) (lb,ub) -> if w >= 0 then (lb, ub+w) else (lb+w, ub)) (0,0) xs'
    ds :: V.Vector w
    ds = V.scanr1 (\w d -> if w /= 0 then gcd w d else d) (V.map snd xs')

    f :: (Int, w) -> Sig (Int, w)
    f (!i, !k)
      | not (lb <= k && k <= ub) = SLeaf False
      | i == V.length xs' && 0 == k = SLeaf True
      | d /= 0 && k `mod` d /= 0 = SLeaf False
      | otherwise = SBranch x (i+1, k) (i+1, k-w)
      where
        (lb,ub) = ys V.! i
        (x, w) = xs' V.! i
        d = ds V.! i

-- | Select subsets that contain a particular element and then remove the element from them
--
-- >>> toSetOfIntSets $ subset1 2 (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [2,4]]) :: ZDD AscOrder)
-- fromList [fromList [1,3],fromList [4]]
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
--
-- >>> toSetOfIntSets $ subset0 2 (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [2,4], [3,4]]) :: ZDD AscOrder)
-- fromList [fromList [1,3],fromList [3,4]]
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
--
-- >>> toSetOfIntSets (insert (IntSet.fromList [1,2,3]) (fromListOfIntSets (map IntSet.fromList [[1,3], [2,4]])) :: ZDD AscOrder)
-- fromList [fromList [1,2,3],fromList [1,3],fromList [2,4]]
insert :: forall a. ItemOrder a => IntSet -> ZDD a -> ZDD a
insert xs = f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs))
  where
    f [] (Leaf _) = Base
    f [] (Branch top p0 p1) = Branch top (f [] p0) p1
    f (y : ys) Empty = Branch y Empty (f ys Empty)
    f (y : ys) Base = Branch y Base (f ys Empty)
    f yys@(y : ys) p@(Branch top p0 p1) =
      case compareItem (Proxy :: Proxy a) y top of
        LT -> Branch y p (f ys Empty)
        GT -> Branch top (f yys p0) p1
        EQ -> Branch top p0 (f ys p1)

-- | Delete a set from the ZDD.
--
-- >>> toSetOfIntSets (delete (IntSet.fromList [1,3]) (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [2,4]])) :: ZDD AscOrder)
-- fromList [fromList [1,2,3],fromList [2,4]]
delete :: forall a. ItemOrder a => IntSet -> ZDD a -> ZDD a
delete xs = f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs))
  where
    f [] (Leaf _) = Empty
    f [] (Branch top p0 p1) = Branch top (f [] p0) p1
    f (_ : _) l@(Leaf _) = l
    f yys@(y : ys) p@(Branch top p0 p1) =
      case compareItem (Proxy :: Proxy a) y top of
        LT -> p
        GT -> Branch top (f yys p0) p1
        EQ -> Branch top p0 (f ys p1)

-- | Insert an item into each element set of ZDD.
--
-- >>> toSetOfIntSets (mapInsert 2 (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [1,4]])) :: ZDD AscOrder)
-- fromList [fromList [1,2,3],fromList [1,2,4]]
mapInsert :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
mapInsert var zdd = runST $ do
  unionOp <- mkUnionOp
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
              EQ -> liftM (Branch top Empty) (unionOp p0 p1)
            H.insert h p ret
            return ret
  f zdd

-- | Delete an item from each element set of ZDD.
--
-- >>> toSetOfIntSets (mapDelete 2 (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [1,2,4]])) :: ZDD AscOrder)
-- fromList [fromList [1,3],fromList [1,4]]
mapDelete :: forall a. ItemOrder a => Int -> ZDD a -> ZDD a
mapDelete var zdd = runST $ do
  unionOp <- mkUnionOp
  h <- C.newSized defaultTableSize
  let f l@(Leaf _) = return l
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) top var of
              GT -> return p
              LT -> liftM2 (Branch top) (f p0) (f p1)
              EQ -> unionOp p0 p1
            H.insert h p ret
            return ret
  f zdd

-- | @change x p@ returns {if x∈s then s∖{x} else s∪{x} | s∈P}
--
-- >>> toSetOfIntSets (change 2 (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [1,2,4]])) :: ZDD AscOrder)
-- fromList [fromList [1,2,3],fromList [1,3],fromList [1,4]]
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
  op <- mkUnionOp
  op zdd1 zdd2

mkUnionOp :: forall a s. ItemOrder a => ST s (ZDD a -> ZDD a -> ST s (ZDD a))
mkUnionOp = do
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
              ZDDCase2EQ2 _ _ -> error "union: should not happen"
            H.insert h key ret
            return ret
  return f

-- | Unions of a list of ZDDs.
unions :: forall f a. (Foldable f, ItemOrder a) => f (ZDD a) -> ZDD a
unions xs = runST $ do
  op <- mkUnionOp
  foldM op empty xs

-- | Intersection of two family of sets.
intersection :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
intersection zdd1 zdd2 = runST $ do
  op <- mkIntersectionOp
  op zdd1 zdd2

mkIntersectionOp :: forall a s. ItemOrder a => ST s (ZDD a -> ZDD a -> ST s (ZDD a))
mkIntersectionOp = do
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
              ZDDCase2EQ2 _ _ -> error "intersection: should not happen"
            H.insert h key ret
            return ret
  return f

-- | Difference of two family of sets.
difference :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
difference zdd1 zdd2 = runST $ do
  op <- mkDifferenceOp
  op zdd1 zdd2

mkDifferenceOp :: forall a s. ItemOrder a => ST s (ZDD a -> ZDD a -> ST s (ZDD a))
mkDifferenceOp = do
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
              ZDDCase2EQ2 _ _ -> error "difference: should not happen"
            H.insert h (p, q) ret
            return ret
  return f

-- | See 'difference'
(\\) :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
m1 \\ m2 = difference m1 m2

-- | Given a family P and Q, it computes {S∈P | ∀X∈Q. X⊈S}
--
-- Sometimes it is denoted as /P ↘ Q/.
--
-- >>> toSetOfIntSets (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [3,4]]) `nonSuperset` singleton (IntSet.fromList [1,3]) :: ZDD AscOrder)
-- fromList [fromList [3,4]]
nonSuperset :: forall a. ItemOrder a => ZDD a -> ZDD a -> ZDD a
nonSuperset zdd1 zdd2 = runST $ do
  op <- mkNonSupersetOp
  op zdd1 zdd2

mkNonSupersetOp :: forall a s. ItemOrder a => ST s (ZDD a -> ZDD a -> ST s (ZDD a))
mkNonSupersetOp = do
  intersectionOp <- mkIntersectionOp
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
                r0 <- f p1 q0
                r1 <- f p1 q1
                liftM2 (Branch top) (f p0 q0) (intersectionOp r0 r1)
              ZDDCase2EQ2 _ _ -> error "nonSuperset: should not happen"
            H.insert h (p, q) ret
            return ret
  return f

minimalHittingSetsKnuth' :: forall a. ItemOrder a => Bool -> ZDD a -> ZDD a
minimalHittingSetsKnuth' imai zdd = runST $ do
  unionOp <- mkUnionOp
  diffOp <- if imai then mkDifferenceOp else mkNonSupersetOp
  h <- C.newSized defaultTableSize
  let f Empty = return Base
      f Base = return Empty
      f p@(Branch top p0 p1) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f =<< unionOp p0 p1
            r1 <- join $ liftM2 diffOp (f p0) (pure r0)
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
hittingSetsBDD = fold' (\top h0 h1 -> h0 BDD..&&. BDD.Branch top h1 BDD.true) (\b -> BDD.Leaf (not b))

minimal :: forall a. ItemOrder a => BDD.BDD a -> ZDD a
minimal bdd = runST $ do
  diffOp <- mkDifferenceOp
  h <- C.newSized defaultTableSize
  let f (BDD.Leaf b) = return (Leaf b)
      f p@(BDD.Branch x lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            ml <- f lo
            mh <- f hi
            ret <- liftM (Branch x ml) (diffOp mh ml)
            H.insert h p ret
            return ret
  f bdd

-- | See 'minimalHittingSetsToda'.
--
-- >>> toSetOfIntSets (minimalHittingSets (fromListOfIntSets (map IntSet.fromList [[1], [2,3,5], [2,3,6], [2,4,5], [2,4,6]]) :: ZDD AscOrder))
-- fromList [fromList [1,2],fromList [1,3,4],fromList [1,5,6]]
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
--
-- Any 'Integral' type can be used as a result type, but it is recommended to use
-- 'Integer' or 'Natural' because the size can be larger than @Int64@ for example:
--
-- >>> size (subsets (IntSet.fromList [1..128]) :: ZDD AscOrder) :: Integer
-- 340282366920938463463374607431768211456
-- >>> import Data.Int
-- >>> maxBound :: Int64
-- 9223372036854775807
--
size :: (Integral b) => ZDD a -> b
size = fold' (\_ n0 n1 -> n0 + n1) (\b -> if b then 1 else 0)

-- | @(s1 `isSubsetOf` s2)@ indicates whether @s1@ is a subset of @s2@.
isSubsetOf :: ItemOrder a => ZDD a -> ZDD a -> Bool
isSubsetOf a b = union a b == b

-- | @(s1 `isProperSubsetOf` s2)@ indicates whether @s1@ is a proper subset of @s2@.
isProperSubsetOf :: ItemOrder a => ZDD a -> ZDD a -> Bool
isProperSubsetOf a b = a `isSubsetOf` b && a /= b

-- | Check whether two sets are disjoint (i.e., their intersection is empty).
disjoint :: ItemOrder a => ZDD a -> ZDD a -> Bool
disjoint a b = null (a `intersection` b)

-- | Count the number of nodes in a ZDD viewed as a rooted directed acyclic graph.
--
-- Please do not confuse it with 'size'.
--
-- See also 'toGraph'.
numNodes :: ZDD a -> Int
numNodes (ZDD node) = Node.numNodes node

-- | Unions of all member sets
--
-- >>> flatten (fromListOfIntSets (map IntSet.fromList [[1,2,3], [1,3], [3,4]]) :: ZDD AscOrder)
-- fromList [1,2,3,4]
flatten :: ItemOrder a => ZDD a -> IntSet
flatten = fold' (\top lo hi -> IntSet.insert top (lo `IntSet.union` hi)) (const IntSet.empty)

-- | Create a ZDD from a set of 'IntSet'
fromSetOfIntSets :: forall a. ItemOrder a => Set IntSet -> ZDD a
fromSetOfIntSets = fromListOfIntSets . Set.toList

-- | Convert the family to a set of 'IntSet'.
toSetOfIntSets :: ZDD a -> Set IntSet
toSetOfIntSets = fold' (\top lo hi -> lo <> Set.map (IntSet.insert top) hi) (\b -> if b then Set.singleton IntSet.empty else Set.empty)

-- | Create a ZDD from a list of 'IntSet'
fromListOfIntSets :: forall a. ItemOrder a => [IntSet] -> ZDD a
fromListOfIntSets = fromListOfSortedList . map f
  where
    f :: IntSet -> [Int]
    f = sortBy (compareItem (Proxy :: Proxy a)) . IntSet.toList

-- | Convert the family to a list of 'IntSet'.
toListOfIntSets :: ZDD a -> [IntSet]
toListOfIntSets = g . fold' f (\b -> (b,[]))
  where
    f top (b, xss) hi = (b, map (IntSet.insert top) (g hi) <> xss)
    g (True, xss) = IntSet.empty : xss
    g (False, xss) = xss

fromListOfSortedList :: forall a. ItemOrder a => [[Int]] -> ZDD a
fromListOfSortedList = unions . map f
  where
    f :: [Int] -> ZDD a
    f = foldr (\x node -> Branch x Empty node) Base

-- | Fold over the graph structure of the ZDD.
--
-- It takes two functions that substitute 'Branch'  and 'Leaf' respectively.
--
-- Note that its type is isomorphic to @('Sig' b -> b) -> ZDD a -> b@.
fold :: (Int -> b -> b -> b) -> (Bool -> b) -> ZDD a -> b
fold br lf (ZDD node) = Node.fold br lf node

-- | Strict version of 'fold'
fold' :: (Int -> b -> b -> b) -> (Bool -> b) -> ZDD a -> b
fold' br lf (ZDD node) = Node.fold' br lf node

-- ------------------------------------------------------------------------

unfoldHashable :: forall a b. (ItemOrder a, Eq b, Hashable b) => (b -> Sig b) -> b -> ZDD a
unfoldHashable f b = runST $ do
  h <- C.newSized defaultTableSize
  let g [] = return ()
      g (x : xs) = do
        r <- H.lookup h x
        case r of
          Just _ -> g xs
          Nothing -> do
            let fx = f x
            H.insert h x fx
            g (xs ++ Foldable.toList fx)
  g [b]
  xs <- H.toList h
  let h2 = HashMap.fromList [(x, inSig (fmap (h2 HashMap.!) s)) | (x,s) <- xs]
  return $ h2 HashMap.! b

unfoldOrd :: forall a b. (ItemOrder a, Ord b) => (b -> Sig b) -> b -> ZDD a
unfoldOrd f b = m2 Map.! b
  where
    m1 :: Map b (Sig b)
    m1 = g Map.empty [b]

    m2 :: Map b (ZDD a)
    m2 = Map.map (inSig . fmap (m2 Map.!)) m1

    g m [] = m
    g m (x : xs) =
      case Map.lookup x m of
        Just _ -> g m xs
        Nothing ->
          let fx = f x
           in g (Map.insert x fx m) (xs ++ Foldable.toList fx)

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
    fold' f (\b -> if b then Just (0, IntSet.empty) else Nothing)
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
--
-- >>> findMaxSum (IntMap.fromList [(1,2),(2,4),(3,-3)] IntMap.!) (fromListOfIntSets (map IntSet.fromList [[1], [2], [3], [1,2,3]]) :: ZDD AscOrder)
-- (4,fromList [2])
findMaxSum :: forall a w. (ItemOrder a, Num w, Ord w) => (Int -> w) -> ZDD a -> (w, IntSet)
findMaxSum weight =
  fromMaybe (error "Data.DecisionDiagram.ZDD.findMinSum: empty ZDD") .
    fold' f (\b -> if b then Just (0, IntSet.empty) else Nothing)
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

-- | Synonym of @'SLeaf' False@
pattern SEmpty :: Sig a
pattern SEmpty = SLeaf False

-- | Synonym of @'SLeaf' True@
pattern SBase :: Sig a
pattern SBase = SLeaf True

-- | 'Sig'-algebra stucture of 'ZDD', \(\mathrm{in}_\mathrm{Sig}\).
inSig :: Sig (ZDD a) -> ZDD a
inSig (SLeaf b) = Leaf b
inSig (SBranch x lo hi) = Branch x lo hi

-- | 'Sig'-coalgebra stucture of 'ZDD', \(\mathrm{out}_\mathrm{Sig}\).
outSig :: ZDD a -> Sig (ZDD a)
outSig (Leaf b) = SLeaf b
outSig (Branch x lo hi) = SBranch x lo hi

-- ------------------------------------------------------------------------

type Graph f = IntMap (f Int)

-- | Convert a ZDD into a pointed graph
--
-- Nodes @0@ and @1@ are reserved for @SLeaf False@ and @SLeaf True@ even if
-- they are not actually used. Therefore the result may be larger than
-- 'numNodes' if the leaf nodes are not used.
toGraph :: ZDD a -> (Graph Sig, Int)
toGraph bdd =
  case toGraph' (Identity bdd) of
    (g, Identity v) -> (g, v)

-- | Convert multiple ZDDs into a graph
toGraph' :: Traversable t => t (ZDD a) -> (Graph Sig, t Int)
toGraph' bs = runST $ do
  h <- C.newSized defaultTableSize
  H.insert h Empty 0
  H.insert h Base 1
  counter <- newSTRef 2
  ref <- newSTRef $ IntMap.fromList [(0, SLeaf False), (1, SLeaf True)]

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
            modifySTRef' ref (IntMap.insert n (SBranch x r0 r1))
            return n

  vs <- mapM f bs
  g <- readSTRef ref
  return (g, vs)

-- | Convert a pointed graph into a ZDD
fromGraph :: (Graph Sig, Int) -> ZDD a
fromGraph (g, v) =
  case IntMap.lookup v (fromGraph' g) of
    Nothing -> error ("Data.DecisionDiagram.ZDD.fromGraph: invalid node id " ++ show v)
    Just bdd -> bdd

-- | Convert nodes of a graph into ZDDs
fromGraph' :: Graph Sig -> IntMap (ZDD a)
fromGraph' g = ret
  where
    ret = IntMap.map f g
    f (SLeaf b) = Leaf b
    f (SBranch x lo hi) =
      case (IntMap.lookup lo ret, IntMap.lookup hi ret) of
        (Nothing, _) -> error ("Data.DecisionDiagram.ZDD.fromGraph': invalid node id " ++ show lo)
        (_, Nothing) -> error ("Data.DecisionDiagram.ZDD.fromGraph': invalid node id " ++ show hi)
        (Just lo', Just hi') -> Branch x lo' hi'

-- ------------------------------------------------------------------------
