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
  , DefaultOrder
  , AscOrder
  , DescOrder
  , withDefaultOrder
  , withAscOrder
  , withDescOrder
  , withCustomOrder

  -- * Level
  , Level (..)
  ) where

import Data.Proxy
import Data.Reflection

-- ------------------------------------------------------------------------

class ItemOrder a where
  compareItem :: proxy a -> Int -> Int -> Ordering

type DefaultOrder = AscOrder

data AscOrder

data DescOrder

instance ItemOrder AscOrder where
  compareItem _ = compare

instance ItemOrder DescOrder where
  compareItem _ = flip compare

data CustomOrder a

instance Reifies s (Int -> Int -> Ordering) => ItemOrder (CustomOrder s) where
  compareItem _ = reflect (Proxy :: Proxy s)

withAscOrder :: forall r. (forall a. ItemOrder a => Proxy a -> r) -> r
withAscOrder k = k (Proxy :: Proxy AscOrder)

withDescOrder :: forall r. (forall a. ItemOrder a => Proxy a -> r) -> r
withDescOrder k = k (Proxy :: Proxy DescOrder)

withDefaultOrder :: forall r. (forall a. ItemOrder a => Proxy a -> r) -> r
withDefaultOrder k = k (Proxy :: Proxy DefaultOrder)

withCustomOrder :: forall r. (Int -> Int -> Ordering) -> (forall a. ItemOrder a => Proxy a -> r) -> r
withCustomOrder cmp k = reify cmp (\(_ :: Proxy s) -> k (Proxy :: Proxy (CustomOrder s)))

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
