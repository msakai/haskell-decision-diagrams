{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
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

import Data.Proxy
import Data.Reflection

-- ------------------------------------------------------------------------

class ItemOrder a where
  compareItem :: proxy a -> Int -> Int -> Ordering

data AscOrder

data DescOrder

instance ItemOrder AscOrder where
  compareItem _ = compare

instance ItemOrder DescOrder where
  compareItem _ = flip compare

data CustomOrder a

instance Reifies s (Int -> Int -> Ordering) => ItemOrder (CustomOrder s) where
  compareItem _ = reflect (Proxy :: Proxy s)

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
