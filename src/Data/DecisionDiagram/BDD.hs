{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
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
    BDD (Leaf, Branch)

  -- * Item ordering
  , ItemOrder (..)
  , AscOrder
  , DescOrder
  , withDefaultOrder
  , withAscOrder
  , withDescOrder
  , withCustomOrder

  -- * Boolean operations
  , true
  , false
  , var
  , notB
  , (.&&.)
  , (.||.)
  , xor
  , (.=>.)
  , (.<=>.)
  , ite
  , andB
  , orB

  -- * Pseudo-boolean constraints
  , pbAtLeast
  , pbAtMost
  , pbExactly
  , pbExactlyIntegral

  -- * Quantification
  , forAll
  , exists
  , existsUnique
  , forAllSet
  , existsSet
  , existsUniqueSet

  -- * Query
  , support
  , evaluate
  , numNodes

  -- * Restriction / Cofactor
  , restrict
  , restrictSet
  , restrictLaw

  -- * Substition / Composition
  , subst
  , substSet

  -- * Satisfiability
  , anySat
  , allSat
  , anySatComplete
  , allSatComplete
  , countSat
  , uniformSatM

  -- * (Co)algebraic structure
  , Sig (..)
  , inSig
  , outSig

  -- * Fold
  , fold
  , fold'

  -- * Unfold
  , unfoldHashable
  , unfoldOrd

  -- * Fixpoints
  , lfp
  , gfp

  -- * Conversion from/to graphs
  , Graph
  , toGraph
  , toGraph'
  , fromGraph
  , fromGraph'
  ) where

import Control.Exception (assert)
import Control.Monad
#if !MIN_VERSION_mwc_random(0,15,0)
import Control.Monad.Primitive
#endif
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Bits (Bits (shiftL))
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Identity
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortBy)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Proxy
import Data.Ratio
import Data.STRef
import qualified Data.Vector as V
import GHC.Generics (Generic)
import Numeric.Natural
#if MIN_VERSION_mwc_random(0,15,0)
import System.Random.MWC (Uniform (..))
import System.Random.Stateful (StatefulGen (..))
#else
import System.Random.MWC (Gen, Variate (..))
#endif
import System.Random.MWC.Distributions (bernoulli)
import Text.Read

import Data.DecisionDiagram.BDD.Internal.ItemOrder
import qualified Data.DecisionDiagram.BDD.Internal.Node as Node

infixr 3 .&&.
infixr 2 .||.
infixr 1 .=>.
infix 1 .<=>.

-- ------------------------------------------------------------------------

defaultTableSize :: Int
defaultTableSize = 256

-- ------------------------------------------------------------------------

-- | Reduced ordered binary decision diagram representing boolean function
newtype BDD a = BDD Node.Node
  deriving (Eq, Hashable)

pattern F :: BDD a
pattern F = Leaf False

pattern T :: BDD a
pattern T = Leaf True

pattern Leaf :: Bool -> BDD a
pattern Leaf b = BDD (Node.Leaf b)

-- | Smart constructor that takes the BDD reduction rules into account
pattern Branch :: Int -> BDD a -> BDD a -> BDD a
pattern Branch x lo hi <- BDD (Node.Branch x (BDD -> lo) (BDD -> hi)) where
  Branch x (BDD lo) (BDD hi)
    | lo == hi = BDD lo
    | otherwise = BDD (Node.Branch x lo hi)

{-# COMPLETE T, F, Branch #-}
{-# COMPLETE Leaf, Branch #-}

nodeId :: BDD a -> Int
nodeId (BDD node) = Node.nodeId node

data BDDCase2 a
  = BDDCase2LT Int (BDD a) (BDD a)
  | BDDCase2GT Int (BDD a) (BDD a)
  | BDDCase2EQ Int (BDD a) (BDD a) (BDD a) (BDD a)
  | BDDCase2EQ2 Bool Bool

bddCase2 :: forall a. ItemOrder a => Proxy a -> BDD a -> BDD a -> BDDCase2 a
bddCase2 _ (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compareItem (Proxy :: Proxy a) ptop qtop of
    LT -> BDDCase2LT ptop p0 p1
    GT -> BDDCase2GT qtop q0 q1
    EQ -> BDDCase2EQ ptop p0 p1 q0 q1
bddCase2 _ (Branch ptop p0 p1) _ = BDDCase2LT ptop p0 p1
bddCase2 _ _ (Branch qtop q0 q1) = BDDCase2GT qtop q0 q1
bddCase2 _ (Leaf b1) (Leaf b2) = BDDCase2EQ2 b1 b2

level :: BDD a -> Level a
level (Branch x _ _) = NonTerminal x
level (Leaf _) = Terminal

-- ------------------------------------------------------------------------

instance Show (BDD a) where
  showsPrec d a   = showParen (d > 10) $
    showString "fromGraph " . shows (toGraph a)

instance Read (BDD a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromGraph" <- lexP
    gv <- readPrec
    return (fromGraph gv)

  readListPrec = readListPrecDefault

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
  let f (Leaf b) = return (Leaf (not b))
      f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- liftM2 (Branch ind) (f lo) (f hi)
            H.insert h n ret
            return ret
  f bdd

apply :: forall a. ItemOrder a => Bool -> (BDD a -> BDD a -> Maybe (BDD a)) -> BDD a -> BDD a -> BDD a
apply isCommutative func bdd1 bdd2 = runST $ do
  op <- mkApplyOp isCommutative func
  op bdd1 bdd2

mkApplyOp :: forall a s. ItemOrder a => Bool -> (BDD a -> BDD a -> Maybe (BDD a)) -> ST s (BDD a -> BDD a -> ST s (BDD a))
mkApplyOp isCommutative func = do
  h <- C.newSized defaultTableSize
  let f a b | Just c <- func a b = return c
      f n1 n2 = do
        let key = if isCommutative && nodeId n2 < nodeId n1 then (n2, n1) else (n1, n2)
        m <- H.lookup h key
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case bddCase2 (Proxy :: Proxy a) n1 n2 of
              BDDCase2GT x2 lo2 hi2 -> liftM2 (Branch x2) (f n1 lo2) (f n1 hi2)
              BDDCase2LT x1 lo1 hi1 -> liftM2 (Branch x1) (f lo1 n2) (f hi1 n2)
              BDDCase2EQ x lo1 hi1 lo2 hi2 -> liftM2 (Branch x) (f lo1 lo2) (f hi1 hi2)
              BDDCase2EQ2 _ _ -> error "apply: should not happen"
            H.insert h key ret
            return ret
  return f

-- | Conjunction of two boolean function
(.&&.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.&&.) bdd1 bdd2 = runST $ do
  op <- mkAndOp
  op bdd1 bdd2

mkAndOp :: forall a s. ItemOrder a => ST s (BDD a -> BDD a -> ST s (BDD a))
mkAndOp = mkApplyOp True f
  where
    f T b = Just b
    f F _ = Just F
    f a T = Just a
    f _ F = Just F
    f a b | a == b = Just a
    f _ _ = Nothing

-- | Disjunction of two boolean function
(.||.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.||.) bdd1 bdd2 = runST $ do
  op <- mkOrOp
  op bdd1 bdd2

mkOrOp :: forall a s. ItemOrder a => ST s (BDD a -> BDD a -> ST s (BDD a))
mkOrOp = mkApplyOp True f
  where
    f T _ = Just T
    f F b = Just b
    f _ T = Just T
    f a F = Just a
    f a b | a == b = Just a
    f _ _ = Nothing

-- | XOR
xor :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
xor bdd1 bdd2 = runST $ do
  op <- mkXOROp
  op bdd1 bdd2

mkXOROp :: forall a s. ItemOrder a => ST s (BDD a -> BDD a -> ST s (BDD a))
mkXOROp = mkApplyOp True f
  where
    f F b = Just b
    f a F = Just a
    f a b | a == b = Just F
    f _ _ = Nothing

-- | Implication
(.=>.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.=>.) = apply False f
  where
    f F _ = Just T
    f T b = Just b
    f _ T = Just T
    f a b | a == b = Just T
    f _ _ = Nothing

-- | Equivalence
(.<=>.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.<=>.) = apply True f
  where
    f (Leaf b1) (Leaf b2) = Just (Leaf (b1 == b2))
    f a b | a == b = Just T
    f _ _ = Nothing

-- | If-then-else
ite :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a -> BDD a
ite c' t' e' = runST $ do
  h <- C.newSized defaultTableSize
  let f (Leaf b) t e = if b then return t else return e
      f _ t e | t == e = return t
      f c t e = do
        case minimum [level c, level t, level e] of
          Terminal -> error "should not happen"
          NonTerminal x -> do
            let key = (c, t, e)
            m <- H.lookup h key
            case m of
              Just y -> return y
              Nothing -> do
                let (c0, c1) = case c of{ Branch x' lo hi | x' == x -> (lo, hi); _ -> (c, c) }
                    (t0, t1) = case t of{ Branch x' lo hi | x' == x -> (lo, hi); _ -> (t, t) }
                    (e0, e1) = case e of{ Branch x' lo hi | x' == x -> (lo, hi); _ -> (e, e) }
                ret <- liftM2 (Branch x) (f c0 t0 e0) (f c1 t1 e1)
                H.insert h key ret
                return ret
  f c' t' e'

-- | Conjunction of a list of BDDs.
andB :: forall f a. (Foldable f, ItemOrder a) => f (BDD a) -> BDD a
andB xs = runST $ do
  op <- mkAndOp
  foldM op true xs

-- | Disjunction of a list of BDDs.
orB :: forall f a. (Foldable f, ItemOrder a) => f (BDD a) -> BDD a
orB xs = runST $ do
  op <- mkOrOp
  foldM op false xs

-- ------------------------------------------------------------------------

-- | Pseudo-boolean constraint, /w1*x1 + w2*x2 + … ≥ k/.
pbAtLeast :: forall a w. (ItemOrder a, Real w) => IntMap w -> w -> BDD a
pbAtLeast xs k0 = unfoldOrd f (0, k0)
  where
    xs' :: V.Vector (Int, w)
    xs' = V.fromList $ sortBy (compareItem (Proxy :: Proxy a) `on` fst) $ IntMap.toList xs
    ys :: V.Vector (w, w)
    ys = V.scanr (\(_, w) (lb,ub) -> if w >= 0 then (lb, ub+w) else (lb+w, ub)) (0,0) xs'

    f :: (Int, w) -> Sig (Int, w)
    f (!i, !k)
      | not (k <= ub) = SLeaf False
      | i == V.length xs' && 0 >= k = SLeaf True
      | lb >= k = SLeaf True -- all remaining variables are don't-care
      | otherwise = SBranch x (i+1, k) (i+1, k-w)
      where
        (lb,ub) = ys V.! i
        (x, w) = xs' V.! i

-- | Pseudo-boolean constraint, /w1*x1 + w2*x2 + … ≤ k/.
pbAtMost :: forall a w. (ItemOrder a, Real w) => IntMap w -> w -> BDD a
pbAtMost xs k0 = unfoldOrd f (0, k0)
  where
    xs' :: V.Vector (Int, w)
    xs' = V.fromList $ sortBy (compareItem (Proxy :: Proxy a) `on` fst) $ IntMap.toList xs
    ys :: V.Vector (w, w)
    ys = V.scanr (\(_, w) (lb,ub) -> if w >= 0 then (lb, ub+w) else (lb+w, ub)) (0,0) xs'

    f :: (Int, w) -> Sig (Int, w)
    f (!i, !k)
      | not (lb <= k) = SLeaf False
      | i == V.length xs' && 0 <= k = SLeaf True
      | ub <= k = SLeaf True -- all remaining variables are don't-care
      | otherwise = SBranch x (i+1, k) (i+1, k-w)
      where
        (lb,ub) = ys V.! i
        (x, w) = xs' V.! i

-- | Pseudo-boolean constraint, /w1*x1 + w2*x2 + … = k/.
--
-- If weight type is 'Integral', 'pbExactlyIntegral' is more efficient.
pbExactly :: forall a w. (ItemOrder a, Real w) => IntMap w -> w -> BDD a
pbExactly xs k0 = unfoldOrd f (0, k0)
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

-- | Similar to 'pbExactly' but more efficient.
pbExactlyIntegral :: forall a w. (ItemOrder a, Real w, Integral w) => IntMap w -> w -> BDD a
pbExactlyIntegral xs k0 = unfoldOrd f (0, k0)
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

-- ------------------------------------------------------------------------

-- | Universal quantification (∀)
forAll :: forall a. ItemOrder a => Int -> BDD a -> BDD a
forAll x bdd = runST $ do
  andOp <- mkAndOp
  h <- C.newSized defaultTableSize
  let f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- if ind == x
                   then andOp lo hi
                   else liftM2 (Branch ind) (f lo) (f hi)
            H.insert h n ret
            return ret
      f a = return a
  f bdd

-- | Existential quantification (∃)
exists :: forall a. ItemOrder a => Int -> BDD a -> BDD a
exists x bdd = runST $ do
  orOp <- mkOrOp
  h <- C.newSized defaultTableSize
  let f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- if ind == x
                   then orOp lo hi
                   else liftM2 (Branch ind) (f lo) (f hi)
            H.insert h n ret
            return ret
      f a = return a
  f bdd

-- | Unique existential quantification (∃!)
existsUnique :: forall a. ItemOrder a => Int -> BDD a -> BDD a
existsUnique x bdd = runST $ do
  xorOp <- mkXOROp
  h <- C.newSized defaultTableSize
  let f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              LT -> liftM2 (Branch ind) (f lo) (f hi)
              EQ -> xorOp lo hi
              GT -> return F
            H.insert h n ret
            return ret
      f _ = return F
  f bdd

-- | Universal quantification (∀) over a set of variables
forAllSet :: forall a. ItemOrder a => IntSet -> BDD a -> BDD a
forAllSet vars bdd = runST $ do
  andOp <- mkAndOp
  h <- C.newSized defaultTableSize
  let f xxs@(x : xs) n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              LT -> liftM2 (Branch ind) (f xxs lo) (f xxs hi)
              EQ -> do
                r0 <- f xs lo
                r1 <- f xs hi
                andOp r0 r1
              GT -> f xs n
            H.insert h n ret
            return ret
      f _ a = return a
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList vars)) bdd

-- | Existential quantification (∃) over a set of variables
existsSet :: forall a. ItemOrder a => IntSet -> BDD a -> BDD a
existsSet vars bdd = runST $ do
  orOp <- mkOrOp
  h <- C.newSized defaultTableSize
  let f xxs@(x : xs) n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              LT -> liftM2 (Branch ind) (f xxs lo) (f xxs hi)
              EQ -> do
                r0 <- f xs lo
                r1 <- f xs hi
                orOp r0 r1
              GT -> f xs n
            H.insert h n ret
            return ret
      f _ a = return a
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList vars)) bdd

-- | Unique existential quantification (∃!) over a set of variables
existsUniqueSet :: forall a. ItemOrder a => IntSet -> BDD a -> BDD a
existsUniqueSet vars bdd = runST $ do
  xorOp <- mkXOROp
  h <- C.newSized defaultTableSize
  let f xxs@(x : xs) n@(Branch ind lo hi) = do
        let key = (xxs, n)
        m <- H.lookup h key
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              LT -> liftM2 (Branch ind) (f xxs lo) (f xxs hi)
              EQ -> do
                r0 <- f xs lo
                r1 <- f xs hi
                xorOp r0 r1
              GT -> return F
            H.insert h key ret
            return ret
      f (_ : _) _ = return F
      f [] a = return a
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList vars)) bdd

-- ------------------------------------------------------------------------

-- | Fold over the graph structure of the BDD.
--
-- It takes two functions that substitute 'Branch'  and 'Leaf' respectively.
--
-- Note that its type is isomorphic to @('Sig' b -> b) -> BDD a -> b@.
fold :: (Int -> b -> b -> b) -> (Bool -> b) -> BDD a -> b
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
fold' :: (Int -> b -> b -> b) -> (Bool -> b) -> BDD a -> b
fold' br lf bdd = runST $ do
  op <- mkFold'Op br lf
  op bdd

mkFold'Op :: (Int -> b -> b -> b) -> (Bool -> b) -> ST s (BDD a -> ST s b)
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

unfoldHashable :: forall a b. (ItemOrder a, Eq b, Hashable b) => (b -> Sig b) -> b -> BDD a
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

unfoldOrd :: forall a b. (ItemOrder a, Ord b) => (b -> Sig b) -> b -> BDD a
unfoldOrd f b = m2 Map.! b
  where
    m1 :: Map b (Sig b)
    m1 = g Map.empty [b]

    m2 :: Map b (BDD a)
    m2 = Map.map (inSig . fmap (m2 Map.!)) m1

    g m [] = m
    g m (x : xs) =
      case Map.lookup x m of
        Just _ -> g m xs
        Nothing ->
          let fx = f x
           in g (Map.insert x fx m) (xs ++ Foldable.toList fx)

-- ------------------------------------------------------------------------

-- | All the variables that this BDD depends on.
support :: BDD a -> IntSet
support bdd = runST $ do
  op <- mkSupportOp
  op bdd

mkSupportOp :: ST s (BDD a -> ST s IntSet)
mkSupportOp = mkFold'Op f g
  where
    f x lo hi = IntSet.insert x (lo `IntSet.union` hi)
    g _ = IntSet.empty

-- | Evaluate a boolean function represented as BDD under the valuation
-- given by @(Int -> Bool)@, i.e. it lifts a valuation function from
-- variables to BDDs.
evaluate :: (Int -> Bool) -> BDD a -> Bool
evaluate f = g
  where
    g (Leaf b) = b
    g (Branch x lo hi)
      | f x = g hi
      | otherwise = g lo

-- | Count the number of nodes in a BDD viewed as a rooted directed acyclic graph.
--
-- See also 'toGraph'.
numNodes :: BDD a -> Int
numNodes (BDD node) = Node.numNodes node

-- ------------------------------------------------------------------------

-- | Compute \(F_x \) or \(F_{\neg x} \).
restrict :: forall a. ItemOrder a => Int -> Bool -> BDD a -> BDD a
restrict x val bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f n@(Leaf _) = return n
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
      f _ n@(Leaf _) = return n
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
      f _ n@(Leaf _) = return n
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
              BDDCase2EQ2 _ _ -> error "restrictLaw: should not happen"
            H.insert h (n1, n2) ret
            return ret
  f law bdd

-- ------------------------------------------------------------------------

-- | @subst x N M@ computes substitution \(M_{x = N}\).
--
-- This operation is also known as /Composition/.
subst :: forall a. ItemOrder a => Int -> BDD a -> BDD a -> BDD a
subst x n m = runST $ do
  h <- C.newSized defaultTableSize
  let f (Branch x' lo _) mhi n2 | x==x' = f lo mhi n2
      f mlo (Branch x' _ hi) n2 | x==x' = f mlo hi n2
      f mlo _ F = return $ restrict x False mlo
      f _ mhi T = return $ restrict x True mhi
      f mlo mhi n2 = do
        u <- H.lookup h (mlo, mhi, n2)
        case u of
          Just y -> return y
          Nothing -> do
            case minimum (map level [mlo, mhi, n2]) of
              Terminal -> error "should not happen"
              NonTerminal x' -> do
                let (mll, mlh) =
                      case mlo of
                        Branch x'' mll' mlh' | x' == x'' -> (mll', mlh')
                        _ -> (mlo, mlo)
                    (mhl, mhh) =
                      case mhi of
                        Branch x'' mhl' mhh' | x' == x'' -> (mhl', mhh')
                        _ -> (mhi, mhi)
                    (n2l, n2h) =
                      case n2 of
                        Branch x'' n2l' n2h' | x' == x'' -> (n2l', n2h')
                        _ -> (n2, n2)
                r0 <- f mll mhl n2l
                r1 <- f mlh mhh n2h
                let ret = Branch x' r0 r1
                H.insert h (mlo, mhi, n2) ret
                return ret
  f m m n

-- | Simultaneous substitution
substSet :: forall a. ItemOrder a => IntMap (BDD a) -> BDD a -> BDD a
substSet s m = runST $ do
  supportOp <- mkSupportOp

  h <- C.newSized defaultTableSize
  let -- f :: IntMap (BDD a) -> [(IntMap Bool, BDD a)] -> IntMap (BDD a) -> ST _ (BDD a)
      f conditions conditioned _ | assert (length conditioned >= 1 && all (\(cond, _) -> IntMap.keysSet cond `IntSet.isSubsetOf` IntMap.keysSet conditions) conditioned) False = undefined
      f conditions conditioned remaining = do
        let l1 = minimum $ map (level . snd) conditioned
            -- remaining' = IntMap.filterWithKey (\x _ -> l1 <= NonTerminal x) remaining
        remaining' <- do
          tmp <- liftM IntSet.unions $ mapM (supportOp . snd) conditioned
          return $ IntMap.restrictKeys remaining tmp
        let l = minimum $ l1 : map level (IntMap.elems remaining' ++ IntMap.elems conditions)
        assert (all (\c -> NonTerminal c <= l) (IntMap.keys conditions)) $ return ()
        case l of
          Terminal -> do
            case propagateFixed conditions conditioned of
              (conditions', conditioned') ->
                assert (IntMap.null conditions' && length conditioned' == 1) $
                  return (snd (head conditioned'))
          NonTerminal x
            | l == l1 && x `IntMap.member` remaining' -> do
                let conditions' = IntMap.insert x (remaining' IntMap.! x) conditions
                    conditioned' = do
                      (cond, a) <- conditioned
                      case a of
                        Branch x' lo hi | x == x' -> [(IntMap.insert x False cond, lo), (IntMap.insert x True cond, hi)]
                        _ -> [(cond, a)]
                f conditions' conditioned' (IntMap.delete x remaining')
            | otherwise -> do
                case propagateFixed conditions conditioned of
                  (conditions', conditioned') -> do
                    let key = (IntMap.toList conditions', [(IntMap.toList cond, a) | (cond, a) <- conditioned'], IntMap.toList remaining')  -- キーを減らせる?
                    u <- H.lookup h key
                    case u of
                      Just y -> return y
                      Nothing -> do
                        let f0 (Branch x' lo _) | x == x' = lo
                            f0 a = a
                            f1 (Branch x' _ hi) | x == x' = hi
                            f1 a = a
                        r0 <- f (IntMap.map f0 conditions') [(cond, f0 a) | (cond, a) <- conditioned'] (IntMap.map f0 remaining')
                        r1 <- f (IntMap.map f1 conditions') [(cond, f1 a) | (cond, a) <- conditioned'] (IntMap.map f1 remaining')
                        let ret = Branch x r0 r1
                        H.insert h key ret
                        return ret
  f IntMap.empty [(IntMap.empty, m)] s

  where
    propagateFixed :: IntMap (BDD a) -> [(IntMap Bool, BDD a)] -> (IntMap (BDD a), [(IntMap Bool, BDD a)])
    propagateFixed conditions conditioned
      | IntMap.null fixed = (conditions, conditioned)
      | otherwise =
          ( IntMap.difference conditions fixed
          , [(IntMap.difference cond fixed, a) | (cond, a) <- conditioned, and $ IntMap.intersectionWith (==) fixed cond]
          )
      where
        fixed = IntMap.mapMaybe asBool conditions

    asBool :: BDD a -> Maybe Bool
    asBool (Leaf b) = Just b
    asBool _ = Nothing

-- ------------------------------------------------------------------------

-- | Least fixed point
lfp :: ItemOrder a => (BDD a ->  BDD a) -> BDD a
lfp f = go false
  where
    go curr
      | curr == next = curr
      | otherwise = go next
      where
        next = f curr

-- | Greatest fixed point
gfp :: ItemOrder a => (BDD a ->  BDD a) -> BDD a
gfp f = go true
  where
    go curr
      | curr == next = curr
      | otherwise = go next
      where
        next = f curr

-- ------------------------------------------------------------------------

findSatM :: MonadPlus m => BDD a -> m (IntMap Bool)
findSatM = fold f g
  where
    f x lo hi = mplus (liftM (IntMap.insert x False) lo) (liftM (IntMap.insert x True) hi)
    g b = if b then return IntMap.empty else mzero

-- | Find one satisfying partial assignment
anySat :: BDD a -> Maybe (IntMap Bool)
anySat = findSatM

-- | Enumerate all satisfying partial assignments
allSat :: BDD a -> [IntMap Bool]
allSat = findSatM

findSatCompleteM :: forall a m. (MonadPlus m, ItemOrder a) => IntSet -> BDD a -> m (IntMap Bool)
findSatCompleteM xs0 bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f _ (Leaf False) = return $ mzero
      f xs (Leaf True) = return $ foldM (\m x -> msum [return (IntMap.insert x v m) | v <- [False, True]]) IntMap.empty xs
      f xs n@(Branch x lo hi) = do
        case span (\x2 -> compareItem (Proxy :: Proxy a) x2 x == LT) xs of
          (ys, (x':xs')) | x == x' -> do
            r <- H.lookup h n
            ps <- case r of
              Just ret -> return ret
              Nothing -> do
                r0 <- f xs' lo
                r1 <- unsafeInterleaveST $ f xs' hi
                let ret = liftM (IntMap.insert x False) r0 `mplus` liftM (IntMap.insert x True) r1
                H.insert h n ret
                return ret
            return $ do
              p <- ps
              foldM (\m y -> msum [return (IntMap.insert y v m) | v <- [False, True]]) p ys
          _ -> error ("findSatCompleteM: " ++ show x ++ " should not occur")
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs0)) bdd

-- | Find one satisfying (complete) assignment over a given set of variables
--
-- The set of variables must be a superset of 'support'.
anySatComplete :: ItemOrder a => IntSet -> BDD a -> Maybe (IntMap Bool)
anySatComplete = findSatCompleteM

-- | Enumerate all satisfying (complete) assignment over a given set of variables
--
-- The set of variables must be a superset of 'support'.
allSatComplete :: ItemOrder a => IntSet -> BDD a -> [IntMap Bool]
allSatComplete = findSatCompleteM

{-# SPECIALIZE countSat :: ItemOrder a => IntSet -> BDD a -> Int #-}
{-# SPECIALIZE countSat :: ItemOrder a => IntSet -> BDD a -> Integer #-}
{-# SPECIALIZE countSat :: ItemOrder a => IntSet -> BDD a -> Natural #-}
-- | Count the number of satisfying (complete) assignment over a given set of variables.
--
-- The set of variables must be a superset of 'support'.
--
-- It is polymorphic in return type, but it is recommended to use 'Integer' or 'Natural'
-- because the size can be larger than fixed integer types such as @Int64@.
--
-- >>> countSat (IntSet.fromList [1..128]) (true :: BDD AscOrder)
-- 340282366920938463463374607431768211456
-- >>> import Data.Int
-- >>> maxBound :: Int64
-- 9223372036854775807
countSat :: forall a b. (ItemOrder a, Num b, Bits b) => IntSet -> BDD a -> b
countSat xs bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f _ (Leaf False) = return $ 0
      f ys (Leaf True) = return $! 1 `shiftL` length ys
      f ys node@(Branch x lo hi) = do
        case span (\x2 -> compareItem (Proxy :: Proxy a) x2 x == LT) ys of
          (zs, y' : ys') | x == y' -> do
            m <- H.lookup h node
            n <- case m of
              Just n -> return n
              Nothing -> do
                n <- liftM2 (+) (f ys' lo) (f ys' hi)
                H.insert h node n
                return n
            return $! n `shiftL` length zs
          (_, _) -> error ("countSat: " ++ show x ++ " should not occur")
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs)) bdd

-- | Sample an assignment from uniform distribution over complete satisfiable assignments ('allSatComplete') of the BDD.
--
-- The function constructs a table internally and the table is shared across
-- multiple use of the resulting action (@m IntSet@).
-- Therefore, the code
--
-- @
-- let g = uniformSatM xs bdd gen
-- s1 <- g
-- s2 <- g
-- @
--
-- is more efficient than
--
-- @
-- s1 <- uniformSatM xs bdd gen
-- s2 <- uniformSatM xs bdd gen
-- @
-- .
#if MIN_VERSION_mwc_random(0,15,0)
uniformSatM :: forall a g m. (ItemOrder a, StatefulGen g m) => IntSet -> BDD a -> g -> m (IntMap Bool)
#else
uniformSatM :: forall a m. (ItemOrder a, PrimMonad m) => IntSet -> BDD a -> Gen (PrimState m) -> m (IntMap Bool)
#endif
uniformSatM xs0 bdd0 = func IntMap.empty
  where
    func = runST $ do
      h <- C.newSized defaultTableSize
      let f xs bdd =
            case span (\x2 -> NonTerminal x2 < level bdd) xs of
              (ys, xxs') -> do
                xs' <- case (bdd, xxs') of
                         (Branch x _ _, x' : xs') | x == x' -> return xs'
                         (Branch x _ _, _) -> error ("uniformSatM: " ++ show x ++ " should not occur")
                         (Leaf _, []) -> return []
                         (Leaf _, _:_) -> error ("uniformSatM: should not happen")
                (s, func0) <- g xs' bdd
                let func' !m !gen = do
#if MIN_VERSION_mwc_random(0,15,0)
                      vals <- replicateM (length ys) (uniformM gen)
#else
                      vals <- replicateM (length ys) (uniform gen)
#endif
                      func0 (m `IntMap.union` IntMap.fromList (zip ys vals)) gen
                return (s `shiftL` length ys, func')
          g _ (Leaf True) = return (1 :: Integer, \a _gen -> return a)
          g _ (Leaf False) = return (0 :: Integer, \_a _gen -> error "uniformSatM: should not happen")
          g xs bdd@(Branch x lo hi) = do
            m <- H.lookup h bdd
            case m of
              Just ret -> return ret
              Nothing -> do
                (n0, func0) <- f xs lo
                (n1, func1) <- f xs hi
                let s = n0 + n1
                    r :: Double
                    r = realToFrac (n1 % s)
                seq r $ return ()
                let func' !a !gen = do
                      b <- bernoulli r gen
                      if b then
                        func1 (IntMap.insert x True a) gen
                      else
                        func0 (IntMap.insert x False a) gen
                H.insert h bdd (s, func')
                return (s, func')
      liftM snd $ f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList xs0)) bdd0

-- ------------------------------------------------------------------------

-- | Signature functor of 'BDD' type
data Sig a
  = SLeaf !Bool
  | SBranch !Int a a
  deriving (Eq, Ord, Show, Read, Generic, Functor, Foldable, Traversable)

instance Hashable a => Hashable (Sig a)

-- | 'Sig'-algebra stucture of 'BDD', \(\mathrm{in}_\mathrm{Sig}\).
inSig :: Sig (BDD a) -> BDD a
inSig (SLeaf b) = Leaf b
inSig (SBranch x lo hi) = Branch x lo hi

-- | 'Sig'-coalgebra stucture of 'BDD', \(\mathrm{out}_\mathrm{Sig}\).
outSig :: BDD a -> Sig (BDD a)
outSig (Leaf b) = SLeaf b
outSig (Branch x lo hi) = SBranch x lo hi

-- ------------------------------------------------------------------------

type Graph f = IntMap (f Int)

-- | Convert a BDD into a pointed graph
--
-- Nodes @0@ and @1@ are reserved for @SLeaf False@ and @SLeaf True@
-- even if they are not actually used. Therefore the result may be
-- larger than 'numNodes' if the leaf nodes are not used.
toGraph :: BDD a -> (Graph Sig, Int)
toGraph bdd =
  case toGraph' (Identity bdd) of
    (g, Identity v) -> (g, v)

-- | Convert multiple BDDs into a graph
toGraph' :: Traversable t => t (BDD a) -> (Graph Sig, t Int)
toGraph' bs = runST $ do
  h <- C.newSized defaultTableSize
  H.insert h F 0
  H.insert h T 1
  counter <- newSTRef 2
  ref <- newSTRef $ IntMap.fromList [(0, SLeaf False), (1, SLeaf True)]

  let f F = return 0
      f T = return 1
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

-- | Convert a pointed graph into a BDD
fromGraph :: (Graph Sig, Int) -> BDD a
fromGraph (g, v) =
  case IntMap.lookup v (fromGraph' g) of
    Nothing -> error ("Data.DecisionDiagram.BDD.fromGraph: invalid node id " ++ show v)
    Just bdd -> bdd

-- | Convert nodes of a graph into BDDs
fromGraph' :: Graph Sig -> IntMap (BDD a)
fromGraph' g = ret
  where
    ret = IntMap.map f g
    f (SLeaf b) = Leaf b
    f (SBranch x lo hi) =
      case (IntMap.lookup lo ret, IntMap.lookup hi ret) of
        (Nothing, _) -> error ("Data.DecisionDiagram.BDD.fromGraph': invalid node id " ++ show lo)
        (_, Nothing) -> error ("Data.DecisionDiagram.BDD.fromGraph': invalid node id " ++ show hi)
        (Just lo', Just hi') -> Branch x lo' hi'

-- ------------------------------------------------------------------------
