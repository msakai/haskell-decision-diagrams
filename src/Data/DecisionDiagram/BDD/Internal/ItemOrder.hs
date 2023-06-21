{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.DecisionDiagram.BDD.Internal.ItemOrder
-- Copyright   :  (c) Masahiro Sakai 2021
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
--
----------------------------------------------------------------------
module Data.DecisionDiagram.BDD.Internal.ItemOrder
  (
  -- * Item ordering
    ItemOrder (..)
  , AscOrder
  , DescOrder
  , withDefaultOrder
  , withAscOrder
  , withDescOrder
  , withCustomOrder

  -- * Ordered item
  , OrderedItem (..)

  -- * Level
  , Level (..)
  ) where

import Data.Function (on)
import Data.Kind (Type)
import Data.List (sortBy)
import Data.Proxy
import Data.Reflection

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet


-- ------------------------------------------------------------------------

class ItemOrder (a :: Type) where
  compareItem :: proxy a -> Int -> Int -> Ordering
  mapToList :: proxy a -> IntMap b -> [(Int,b)]
  setToList :: proxy a -> IntSet -> [Int]

data AscOrder

data DescOrder

instance ItemOrder AscOrder where
  compareItem _ = compare
  mapToList _ = IntMap.toAscList
  setToList _ = IntSet.toAscList

instance ItemOrder DescOrder where
  compareItem _ = flip compare
  mapToList _ = IntMap.toDescList
  setToList _ = IntSet.toDescList

data CustomOrder a

instance Reifies s (Int -> Int -> Ordering) => ItemOrder (CustomOrder s) where
  compareItem _ = reflect (Proxy :: Proxy s)
  mapToList o m = sortBy (compareItem o `on` fst) (IntMap.toList m)
  setToList o s = sortBy (compareItem o) (IntSet.toList s)

withAscOrder :: forall r. (Proxy AscOrder -> r) -> r
withAscOrder k = k Proxy

withDescOrder :: forall r. (Proxy DescOrder -> r) -> r
withDescOrder k = k Proxy

-- | Currently the default order is 'AscOrder'
withDefaultOrder :: forall r. (forall a. ItemOrder a => Proxy a -> r) -> r
withDefaultOrder k = k (Proxy :: Proxy AscOrder)

withCustomOrder :: forall r. (Int -> Int -> Ordering) -> (forall a. ItemOrder a => Proxy a -> r) -> r
withCustomOrder cmp k = reify cmp (\(_ :: Proxy s) -> k (Proxy :: Proxy (CustomOrder s)))

-- ------------------------------------------------------------------------

newtype OrderedItem a = OrderedItem Int
  deriving (Eq, Show)

instance ItemOrder a => Ord (OrderedItem a) where
  compare (OrderedItem x) (OrderedItem y) = compareItem (Proxy :: Proxy a) x y

-- ------------------------------------------------------------------------

data Level a
  = NonTerminal !Int
  | Terminal
  deriving (Eq, Show)

instance ItemOrder a => Ord (Level a) where
  compare (NonTerminal x) (NonTerminal y) = compareItem (Proxy :: Proxy a) x y
  compare (NonTerminal _) Terminal = LT
  compare Terminal (NonTerminal _) = GT
  compare Terminal Terminal = EQ

-- ------------------------------------------------------------------------
