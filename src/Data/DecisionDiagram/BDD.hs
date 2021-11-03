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
  , xor
  , (.=>.)
  , (.<=>.)
  , ite
  , andB
  , orB

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

  -- * Restriction / Cofactor
  , restrict
  , restrictSet
  , restrictLaw

  -- * Substition / Composition
  , subst
  , substSet

  -- * Fold
  , fold
  , fold'

  -- * Conversion from/to graphs
  , Graph
  , Node (..)
  , toGraph
  , toGraph'
  , fromGraph
  , fromGraph'
  ) where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.ST
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Identity
import Data.Hashable
import qualified Data.HashTable.Class as H
import qualified Data.HashTable.ST.Cuckoo as C
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (sortBy)
import Data.Proxy
import Data.STRef
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
  | BDDCase2EQ2 Bool Bool

bddCase2 :: forall a. ItemOrder a => Proxy a -> BDD a -> BDD a -> BDDCase2 a
bddCase2 _ (Branch ptop p0 p1) (Branch qtop q0 q1) =
  case compareItem (Proxy :: Proxy a) ptop qtop of
    LT -> BDDCase2LT ptop p0 p1
    GT -> BDDCase2GT qtop q0 q1
    EQ -> BDDCase2EQ ptop p0 p1 q0 q1
bddCase2 _ (Branch ptop p0 p1) _ = BDDCase2LT ptop p0 p1
bddCase2 _ _ (Branch qtop q0 q1) = BDDCase2GT qtop q0 q1
bddCase2 _ T T = BDDCase2EQ2 True True
bddCase2 _ T F = BDDCase2EQ2 True False
bddCase2 _ F T = BDDCase2EQ2 False True
bddCase2 _ F F = BDDCase2EQ2 False False

level :: BDD a -> Level a
level T = Terminal
level F = Terminal
level (Branch x _ _) = NonTerminal x

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

apply' :: forall a. ItemOrder a => Bool -> (BDD a -> BDD a -> Maybe (BDD a)) -> BDD a -> BDD a -> BDD a
apply' isCommutative func bdd1 bdd2 = runST $ do
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
              BDDCase2EQ2 _ _ -> error "apply': should not happen"
            H.insert h key ret
            return ret
  f bdd1 bdd2

-- | Conjunction of two boolean function
(.&&.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.&&.) = apply' True f
  where
    f T b = Just b
    f F _ = Just F
    f a T = Just a
    f _ F = Just F
    f a b | a == b = Just a
    f _ _ = Nothing

-- | Disjunction of two boolean function
(.||.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.||.) = apply' True f
  where
    f T _ = Just T
    f F b = Just b
    f _ T = Just T
    f a F = Just a
    f a b | a == b = Just a
    f _ _ = Nothing

-- | XOR
xor :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
xor = apply' True f
  where
    f F b = Just b
    f a F = Just a
    f a b | a == b = Just F
    f _ _ = Nothing

-- | Implication
(.=>.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.=>.) = apply' False f
  where
    f F _ = Just T
    f T b = Just b
    f _ T = Just T
    f a b | a == b = Just T
    f _ _ = Nothing

-- | Equivalence
(.<=>.) :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a
(.<=>.) = apply' True f
  where
    f T T = Just T
    f T F = Just F
    f F T = Just F
    f F F = Just T
    f a b | a == b = Just T
    f _ _ = Nothing

-- | If-then-else
ite :: forall a. ItemOrder a => BDD a -> BDD a -> BDD a -> BDD a
ite c' t' e' = runST $ do
  h <- C.newSized defaultTableSize
  let f T t _ = return t
      f F _ e = return e
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
andB xs = Foldable.foldl' (.&&.) true xs

-- | Disjunction of a list of BDDs.
orB :: forall f a. (Foldable f, ItemOrder a) => f (BDD a) -> BDD a
orB xs = Foldable.foldl' (.||.) false xs

-- ------------------------------------------------------------------------

-- | Universal quantification (∀)
forAll :: forall a. ItemOrder a => Int -> BDD a -> BDD a
forAll x bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- if ind == x
                   then return $ lo .&&. hi
                   else liftM2 (Branch ind) (f lo) (f hi)
            H.insert h n ret
            return ret
      f a = return a
  f bdd

-- | Existential quantification (∃)
exists :: forall a. ItemOrder a => Int -> BDD a -> BDD a
exists x bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- if ind == x
                   then return $ lo .||. hi
                   else liftM2 (Branch ind) (f lo) (f hi)
            H.insert h n ret
            return ret
      f a = return a
  f bdd

-- | Unique existential quantification (∃!)
existsUnique :: forall a. ItemOrder a => Int -> BDD a -> BDD a
existsUnique x bdd = runST $ do
  h <- C.newSized defaultTableSize
  let f n@(Branch ind lo hi) = do
        m <- H.lookup h n
        case m of
          Just y -> return y
          Nothing -> do
            ret <- case compareItem (Proxy :: Proxy a) ind x of
              LT -> liftM2 (Branch ind) (f lo) (f hi)
              EQ -> return $ lo `xor` hi
              GT -> return F
            H.insert h n ret
            return ret
      f _ = return F
  f bdd

-- | Universal quantification (∀) over a set of variables
forAllSet :: forall a. ItemOrder a => IntSet -> BDD a -> BDD a
forAllSet vars bdd = runST $ do
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
                return (r0 .&&. r1)
              GT -> f xs n
            H.insert h n ret
            return ret
      f _ a = return a
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList vars)) bdd

-- | Existential quantification (∃) over a set of variables
existsSet :: forall a. ItemOrder a => IntSet -> BDD a -> BDD a
existsSet vars bdd = runST $ do
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
                return (r0 .||. r1)
              GT -> f xs n
            H.insert h n ret
            return ret
      f _ a = return a
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList vars)) bdd

-- | Unique existential quantification (∃!) over a set of variables
existsUniqueSet :: forall a. ItemOrder a => IntSet -> BDD a -> BDD a
existsUniqueSet vars bdd = runST $ do
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
                return (r0 `xor` r1)
              GT -> return F
            H.insert h key ret
            return ret
      f (_ : _) _ = return F
      f [] a = return a
  f (sortBy (compareItem (Proxy :: Proxy a)) (IntSet.toList vars)) bdd

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
  h <- C.newSized defaultTableSize
  let -- f :: IntMap (BDD a) -> [(IntMap Bool, BDD a)] -> IntMap (BDD a) -> ST _ (BDD a)
      f conditions conditioned _ | assert (length conditioned >= 1 && all (\(cond, _) -> IntMap.keysSet cond `IntSet.isSubsetOf` IntMap.keysSet conditions) conditioned) False = undefined
      f conditions conditioned remaining = do
        let l1 = minimum $ map (level . snd) conditioned
            -- remaining' = IntMap.filterWithKey (\x _ -> l1 <= NonTerminal x) remaining
            remaining' = IntMap.restrictKeys remaining (IntSet.unions [support a | (_, a) <- conditioned])
            l = minimum $ l1 : map level (IntMap.elems remaining' ++ IntMap.elems conditions)
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
    asBool a =
      case a of
        T -> Just True
        F -> Just False
        _ -> Nothing

-- ------------------------------------------------------------------------

type Graph = IntMap Node

data Node
  = NodeF
  | NodeT
  | NodeBranch !Int Int Int
  deriving (Eq, Show, Read)

-- | Convert a BDD into a pointed graph
toGraph :: BDD a -> (Graph, Int)
toGraph bdd =
  case toGraph' (Identity bdd) of
    (g, Identity v) -> (g, v)

-- | Convert multiple BDDs into a graph
toGraph' :: Traversable t => t (BDD a) -> (Graph, t Int)
toGraph' bs = runST $ do
  h <- C.newSized defaultTableSize
  H.insert h F 0
  H.insert h T 1
  counter <- newSTRef 2
  ref <- newSTRef $ IntMap.fromList [(0, NodeF), (1, NodeT)]

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
            modifySTRef' ref (IntMap.insert n (NodeBranch x r0 r1))
            return n

  vs <- mapM f bs
  g <- readSTRef ref
  return (g, vs)

-- | Convert a pointed graph into a BDD
fromGraph :: (Graph, Int) -> BDD a
fromGraph (g, v) =
  case IntMap.lookup v (fromGraph' g) of
    Nothing -> error ("Data.DecisionDiagram.BDD.fromGraph: invalid node id " ++ show v)
    Just bdd -> bdd

-- | Convert nodes of a graph into BDDs
fromGraph' :: Graph -> IntMap (BDD a)
fromGraph' g = ret
  where
    ret = IntMap.map f g
    f NodeF = F
    f NodeT = T
    f (NodeBranch x lo hi) =
      case (IntMap.lookup lo ret, IntMap.lookup hi ret) of
        (Nothing, _) -> error ("Data.DecisionDiagram.BDD.fromGraph': invalid node id " ++ show lo)
        (_, Nothing) -> error ("Data.DecisionDiagram.BDD.fromGraph': invalid node id " ++ show hi)
        (Just lo', Just hi') -> Branch x lo' hi'

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
