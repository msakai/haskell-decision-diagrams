{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
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
-- Reduced Ordered Binary Decision Diagrams (ROBDD).
--
-- References:
--
-- * Bryant, "Graph-Based Algorithms for Boolean Function Manipulation,"
--   in IEEE Transactions on Computers, vol. C-35, no. 8, pp. 677-691,
--   Aug. 1986, doi: [10.1109/TC.1986.1676819](https://doi.org/10.1109/TC.1986.1676819).
--   <https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf>
--
----------------------------------------------------------------------
module Data.DecisionDiagram.BDD
  (
  -- * The BDD type
    BDD (BDD, F, T, Branch)

  -- * Item ordering
  , ItemOrder (..)
  , DefaultOrder
  , withDefaultOrder
  , withCustomOrder

  -- * Boolean operations
  , true
  , false
  , var
  , notB
  , (.&&.)
  , (.||.)
  , andB
  , orB

  -- * Query
  , support
  , evaluate

  -- * Restriction / Cofactor
  , restrict
  , restrictSet
  , restrictLaw

  -- * Fold
  , fold
  , fold'
  ) where

import Control.Monad
import Control.Monad.ST
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortBy)
import Data.Proxy

import Data.DecisionDiagram.BDD.Internal.ItemOrder
import qualified Data.DecisionDiagram.BDD.Internal.Node as Node

infixr 3 .&&.
infixr 2 .||.

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Reduced ordered binary decision diagram representing boolean function
newtype BDD a = BDD Node.Node
  deriving (Eq, Hashable, Show)

pattern F :: BDD a
pattern F = BDD Node.F

pattern T :: BDD a
pattern T = BDD Node.T

-- | Smart constructor that takes the BDD reduction rules into account
pattern Branch :: Int -> BDD a -> BDD a -> BDD a
pattern Branch x lo hi <- BDD (Node.Branch x (BDD -> lo) (BDD -> hi)) where
  Branch x (BDD lo) (BDD hi)
    | lo == hi = BDD lo
    | otherwise = BDD (Node.Branch x lo hi)

{-# COMPLETE T, F, Branch #-}

nodeId :: BDD a -> Int
nodeId (BDD node) = Node.nodeId node

data BDDCase2 a
  = BDDCase2LT Int (BDD a) (BDD a)
  | BDDCase2GT Int (BDD a) (BDD a)
  | BDDCase2EQ Int (BDD a) (BDD a) (BDD a) (BDD a)

bddCase2 :: forall a. ItemOrder a => Proxy a -> BDD a -> BDD a -> BDDCase2 a
bddCase2 _ (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compareItem (Proxy :: Proxy a) ptop qtop of
    LT -> BDDCase2LT ptop p0 p1
    GT -> BDDCase2GT qtop q0 q1
    EQ -> BDDCase2EQ ptop p0 p1 q0 q1
bddCase2 _ (Branch ptop p0 p1) _ = BDDCase2LT ptop p0 p1
bddCase2 _ _ (Branch qtop q0 q1) = BDDCase2GT qtop q0 q1
bddCase2 _ _ _ = error "should not happen"

level :: BDD a -> Level a
level T = Terminal
level F = Terminal
level (Branch x _ _) = NonTerminal x

-- ------------------------------------------------------------------------

-- | True
true :: BDD a
true = T

-- | False
false :: BDD a
false = F

-- | A variable \(x_i\)
var :: Int -> BDD a
var ind = Branch ind F T

-- | Negation of a boolean function
notB :: BDD a -> BDD a
notB bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f T = return F
      f F = return T
      f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- liftM2 (Branch ind) (f lo) (f hi)
            H.insert h n ret
            return ret
  f bdd

-- | Conjunction of two boolean function
(.&&.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
bdd1 .&&. bdd2 = runST $ do
  h <- C.newSized defaultTableSize
  let f T b = return b
      f F _ = return F
      f a T = return a
      f _ F = return F
      f a b | a == b = return a
      f n1@(Branch ind1 lo1 hi1) n2@(Branch ind2 lo2 hi2) = do
        let key = if nodeId n1 <= nodeId n2 then (n1, n2) else (n2, n1)
        m <- H.lookup h key
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind1 ind2 of
              EQ -> liftM2 (Branch ind1) (f lo1 lo2) (f hi1 hi2)
              LT -> liftM2 (Branch ind1) (f lo1 n2) (f hi1 n2)
              GT -> liftM2 (Branch ind2) (f n1 lo2) (f n1 hi2)
            H.insert h key ret
            return ret
  f bdd1 bdd2

-- | Disjunction of two boolean function
(.||.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
bdd1 .||. bdd2 = runST $ do
  h <- C.newSized defaultTableSize
  let f T _ = return T
      f F b = return b
      f _ T = return T
      f a F = return a
      f a b | a == b = return a
      f n1@(Branch ind1 lo1 hi1) n2@(Branch ind2 lo2 hi2) = do
        let key = if nodeId n1 <= nodeId n2 then (n1, n2) else (n2, n1)
        m <- H.lookup h key
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind1 ind2 of
              EQ -> liftM2 (Branch ind1) (f lo1 lo2) (f hi1 hi2)
              LT -> liftM2 (Branch ind1) (f lo1 n2) (f hi1 n2)
              GT -> liftM2 (Branch ind2) (f n1 lo2) (f n1 hi2)
            H.insert h key ret
            return ret
  f bdd1 bdd2

-- | Conjunction of a list of BDDs.
andB :: forall f a. (Foldable f, ItemOrder a) => f (BDD a) -> BDD a
andB xs = Foldable.foldl' (.&&.) true xs

-- | Disjunction of a list of BDDs.
orB :: forall f a. (Foldable f, ItemOrder a) => f (BDD a) -> BDD a
orB xs = Foldable.foldl' (.||.) false xs

-- ------------------------------------------------------------------------

-- | Fold over the graph structure of the BDD.
--
-- It takes values for substituting 'false' ('F') and 'true' ('T'),
-- and a function for substiting non-terminal node ('Branch').
fold :: b -> b -> (Int -> b -> b -> b) -> BDD a -> b
fold ff tt br bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return ff
      f T = return tt
      f p@(Branch top lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f lo
            r1 <- f hi
            let ret = br top r0 r1
            H.insert h p ret
            return ret
  f bdd

-- | Strict version of 'fold'
fold' :: b -> b -> (Int -> b -> b -> b) -> BDD a -> b
fold' !ff !tt br bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f F = return ff
      f T = return tt
      f p@(Branch top lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f lo
            r1 <- f hi
            let ret = br top r0 r1
            seq ret $ H.insert h p ret
            return ret
  f bdd

-- ------------------------------------------------------------------------

-- | All the variables that this BDD depends on.
support :: BDD a -> IntSet
support = fold' IntSet.empty IntSet.empty f
  where
    f x lo hi = IntSet.insert x (lo `IntSet.union` hi)

-- | Evaluate a boolean function represented as BDD under the valuation
-- given by @(Int -> Bool)@, i.e. it lifts a valuation function from
-- variables to BDDs.
evaluate :: (Int -> Bool) -> BDD a -> Bool
evaluate f = g
  where
    g F = False
    g T = True
    g (Branch x lo hi)
      | f x = g hi
      | otherwise = g lo

-- ------------------------------------------------------------------------

-- | Compute \(F_x \) or \(F_{\neg x} \).
restrict :: forall a. ItemOrder a => Int -> Bool -> BDD a -> BDD a
restrict x val bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f T = return T
      f F = return F
      f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              GT -> return n
              LT -> liftM2 (Branch ind) (f lo) (f hi)
              EQ -> if val then return hi else return lo
            H.insert h n ret
            return ret
  f bdd

-- | Compute \(F_{\{x_i = v_i\}_i} \).
restrictSet :: forall a. ItemOrder a => IntMap Bool -> BDD a -> BDD a
restrictSet val bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f [] n = return n
      f _ T = return T
      f _ F = return F
      f xxs@((x,v) : xs) n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              GT -> f xs n
              LT -> liftM2 (Branch ind) (f xxs lo) (f xxs hi)
              EQ -> if v then f xs hi else f xs lo
            H.insert h n ret
            return ret
  f (sortBy (compareItem (Proxy :: Proxy a) `on` fst) (IntMap.toList val)) bdd

-- | Compute generalized cofactor of F with respect to C.
--
-- Note that C is the first argument.
restrictLaw :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
restrictLaw law bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f T n = return n
      f F _ = return T  -- Is this correct?
      f _ F = return F
      f _ T = return T
      f n1 n2 | n1 == n2 = return T
      f n1 n2 = do
        m <- H.lookup h (n1, n2)
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case bddCase2 (Proxy :: Proxy a) n1 n2 of
              BDDCase2GT x2 lo2 hi2 -> liftM2 (Branch x2) (f n1 lo2) (f n1 hi2)
              BDDCase2EQ x1 lo1 hi1 lo2 hi2
                | lo1 == F  -> f hi1 hi2
                | hi1 == F  -> f lo1 lo2
                | otherwise -> liftM2 (Branch x1) (f lo1 lo2) (f hi1 hi2)
              BDDCase2LT x1 lo1 hi1
                | lo1 == F  -> f hi1 n2
                | hi1 == F  -> f lo1 n2
                | otherwise -> liftM2 (Branch x1) (f lo1 n2) (f hi1 n2)
            H.insert h (n1, n2) ret
            return ret
  f law bdd

-- ------------------------------------------------------------------------

-- https://ja.wikipedia.org/wiki/%E4%BA%8C%E5%88%86%E6%B1%BA%E5%AE%9A%E5%9B%B3
_test_bdd :: BDD DefaultOrder
_test_bdd = (notB x1 .&&. notB x2 .&&. notB x3) .||. (x1 .&&. x2) .||. (x2 .&&. x3)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
{-
BDD (Node 880 (UBranch 1 (Node 611 (UBranch 2 (Node 836 UT) (Node 215 UF))) (Node 806 (UBranch 2 (Node 842 (UBranch 3 (Node 836 UT) (Node 215 UF))) (Node 464 (UBranch 3 (Node 215 UF) (Node 836 UT)))))))
-}

-- ------------------------------------------------------------------------
