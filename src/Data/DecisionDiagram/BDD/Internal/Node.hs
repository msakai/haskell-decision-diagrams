{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
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
    Node (Leaf, Branch)
  , nodeId

  , numNodes

  -- * Fold
  , fold
  , fold'
  , mkFold'Op

  -- * (Co)algebraic structure
  , Sig (..)

  -- * Graph
  , Graph
  , toGraph
  , toGraph'
  ) where

import Control.Monad
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Functor.Identity
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.Interned
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.STRef
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

pattern Leaf :: Bool -> Node
pattern Leaf b <- (asBool -> Just b) where
  Leaf True = T
  Leaf False = F

asBool :: Node -> Maybe Bool
asBool T = Just True
asBool F = Just False
asBool _ = Nothing

pattern Branch :: Int -> Node -> Node -> Node
pattern Branch ind lo hi <- (unintern -> UBranch ind lo hi) where
  Branch ind lo hi = intern (UBranch ind lo hi)

{-# COMPLETE T, F, Branch #-}
{-# COMPLETE Leaf, Branch #-}

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

defaultTableSize :: Int
defaultTableSize = 256

-- | Counts the number of nodes when viewed as a rooted directed acyclic graph
numNodes :: Node -> Int
numNodes node0 = runST $ do
  h <- C.newSized defaultTableSize
  let f node = do
        m <- H.lookup h node
        case m of
          Just _ -> return ()
          Nothing -> do
            H.insert h node ()
            case node of
              Branch _ lo hi -> f lo >> f hi
              _ -> return ()
  f node0
  liftM length $ H.toList h

-- ------------------------------------------------------------------------

-- | Signature functor of binary decision trees, BDD, and ZDD.
data Sig a
  = SLeaf !Bool
  | SBranch !Int a a
  deriving (Eq, Ord, Show, Read, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Sig a)

-- ------------------------------------------------------------------------

-- | Fold over the graph structure of Node.
--
-- It takes two functions that substitute 'Branch'  and 'Leaf' respectively.
--
-- Note that its type is isomorphic to @('Sig' a -> a) -> 'Node' -> a@.
fold :: (Int -> a -> a -> a) -> (Bool -> a) -> Node -> a
fold br lf bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f (Leaf b) = return (lf b)
      f p@(Branch top lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- unsafeInterleaveST $ f lo
            r1 <- unsafeInterleaveST $ f hi
            let ret = br top r0 r1
            H.insert h p ret  -- Note that H.insert is value-strict
            return ret
  f bdd

-- | Strict version of 'fold'
fold' :: (Int -> a -> a -> a) -> (Bool -> a) -> Node -> a
fold' br lf bdd = runST $ do
  op <- mkFold'Op br lf
  op bdd

mkFold'Op :: (Int -> a -> a -> a) -> (Bool -> a) -> ST s (Node -> ST s a)
mkFold'Op br lf = do
  h <- C.newSized defaultTableSize
  let f (Leaf b) = return $! lf b
      f p@(Branch top lo hi) = do
        m <- H.lookup h p
        case m of
          Just ret -> return ret
          Nothing -> do
            r0 <- f lo
            r1 <- f hi
            let ret = br top r0 r1
            H.insert h p ret  -- Note that H.insert is value-strict
            return ret
  return f

-- ------------------------------------------------------------------------

-- | Graph where nodes are decorated using a functor @f@.
--
-- The occurrences of the parameter of @f@ represent out-going edges.
type Graph f = IntMap (f Int)

-- | Convert a node into a pointed graph
--
-- Nodes @0@ and @1@ are reserved for @SLeaf False@ and @SLeaf True@ even if
-- they are not actually used. Therefore the result may be larger than
-- 'numNodes' if the leaf nodes are not used.
toGraph :: Node -> (Graph Sig, Int)
toGraph bdd =
  case toGraph' (Identity bdd) of
    (g, Identity v) -> (g, v)

-- | Convert multiple nodes into a graph
toGraph' :: Traversable t => t Node -> (Graph Sig, t Int)
toGraph' bs = runST $ do
  h <- C.newSized defaultTableSize
  H.insert h (Leaf False) 0
  H.insert h (Leaf True) 1
  counter <- newSTRef 2
  ref <- newSTRef $ IntMap.fromList [(0, SLeaf False), (1, SLeaf True)]

  let f (Leaf False) = return 0
      f (Leaf True) = return 1
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

-- ------------------------------------------------------------------------
