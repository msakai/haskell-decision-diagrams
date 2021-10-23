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
  , withDefaultOrder
  , withCustomOrder
  ) where

import Data.Proxy
import Data.Reflection

-- ------------------------------------------------------------------------

class ItemOrder a where
  compareItem :: proxy a -> Int -> Int -> Ordering

data DefaultOrder

instance ItemOrder DefaultOrder where
  compareItem _ = compare

data CustomOrder a

instance Reifies s (Int -> Int -> Ordering) => ItemOrder (CustomOrder s) where
  compareItem _ = reflect (Proxy :: Proxy s)

withDefaultOrder :: forall r. (forall a. ItemOrder a => Proxy a -> r) -> r
withDefaultOrder k = k (Proxy :: Proxy DefaultOrder)

withCustomOrder :: forall r. (Int -> Int -> Ordering) -> (forall a. ItemOrder a => Proxy a -> r) -> r
withCustomOrder cmp k = reify cmp (\(_ :: Proxy s) -> k (Proxy :: Proxy (CustomOrder s)))

-- ------------------------------------------------------------------------
