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
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.Proxy

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
