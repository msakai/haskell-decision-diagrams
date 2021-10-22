{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.DecisionDiagram.BDD.Internal.Node
-- Copyright   :  (c) Masahiro Sakai 2021
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  unstable
-- Portability :  non-portable
--
----------------------------------------------------------------------
module Data.DecisionDiagram.BDD.Internal.Node
  (
  -- * Low level node type
    Node (T, F, Branch)
  , nodeId
  ) where

import Data.Hashable
import Data.Interned
import GHC.Generics

-- ------------------------------------------------------------------------

-- | Hash-consed node types in BDD or ZDD
data Node = Node {-# UNPACK #-} !Id UNode
  deriving (Show)

instance Eq Node where
  Node i _ == Node j _ = i == j

instance Hashable Node where
  hashWithSalt s (Node i _) = hashWithSalt s i

pattern T :: Node
pattern T <- (unintern -> UT) where
  T = intern UT

pattern F :: Node
pattern F <- (unintern -> UF) where
  F = intern UF

pattern Branch :: Int -> Node -> Node -> Node
pattern Branch ind lo hi <- (unintern -> UBranch ind lo hi) where
  Branch ind lo hi = intern (UBranch ind lo hi)

{-# COMPLETE T, F, Branch #-}

data UNode
  = UT
  | UF
  | UBranch {-# UNPACK #-} !Int Node Node
  deriving (Show)

instance Interned Node where
  type Uninterned Node = UNode
  data Description Node
    = DT
    | DF
    | DBranch {-# UNPACK #-} !Int {-# UNPACK #-} !Id {-# UNPACK #-} !Id
    deriving (Eq, Generic)
  describe UT = DT
  describe UF = DF
  describe (UBranch x (Node i _) (Node j _)) = DBranch x i j
  identify = Node
  cache = nodeCache

instance Hashable (Description Node)

instance Uninternable Node where
  unintern (Node _ uformula) = uformula

nodeCache :: Cache Node
nodeCache = mkCache
{-# NOINLINE nodeCache #-}

nodeId :: Node -> Id
nodeId (Node id_ _) = id_

-- ------------------------------------------------------------------------
