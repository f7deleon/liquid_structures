{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module BraunTree where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, pow, min, exponent, take, drop, repeat, head, tail, lookup)
import ImprovedList
import Basics

data Tree a where
  Node :: (Eq a) => a -> Tree a -> Tree a -> Tree a
  Nil :: Tree a

deriving instance (Eq a, Show a) => Show (Tree a)

instance (Eq a) => Eq (Tree a) where
  (Node v l r) == (Node v2 l2 r2) = v == v2 && l == l2 && r == r2
  (Nil) == (Nil) = True
  (Node _ _ _) == Nil = False
  Nil == (Node _ _ _) = False

isEmpty :: Array a -> Bool
isEmpty Nil = True
isEmpty _ = False
{-@ reflect isEmpty @-}

{-@ reflect value @-}
{-@ value :: t : ArrayNE a -> a @-}
value :: Array a -> a
value (Node v _ _) = v

{-@ reflect isValue @-}
isValue :: (Eq a) => Array a -> a -> Bool
isValue (Node v _ _) x = v == x
isValue Nil  _ = False

{-@ reflect left @-}
{-@ left :: t: ArrayNE a -> Array a @-}
left :: Array a -> Array a
left (Node _ l _) = l

{-@ reflect right @-}
{-@ right :: t: ArrayNE a -> Array a @-}
right :: Array a -> Array a
right (Node _ _ r) = r

{-@ measure nodeCount @-}
{-@ nodeCount :: t : Tree a -> n : Nat @-}
nodeCount :: Tree a -> Int
nodeCount (Node _ l r) = 1 + nodeCount l + nodeCount r
nodeCount Nil = 0

{-@ measure h @-}
{-@ h :: t: Tree a -> i : { Nat | i >= mh t }  @-}
h :: Tree a -> Int
h (Node _ l r) 
  | hl >= hr = 1 + hl
  | otherwise = 1 + hr
  where 
    hl = h l
    hr = h r
h Nil = 0

{-@ measure mh @-}
{-@ mh :: t : Tree a -> i : { Nat | i <= h t } @-}
mh :: Tree a -> Int
mh (Node _ l r) 
    | ml < mr = 1 + ml
    | otherwise = 1 + mr 
    where
     ml = mh l
     mr = mh r
mh Nil = 0

{-@ measure balanced @-}
{-@ balanced :: t : Tree a -> v : Bool @-}
balanced :: Tree a -> Bool
balanced (Nil) = True
balanced t@(Node _ l r) = balanced l && balanced r && abs (h t - mh t) <= 1 

{-@ type BTree a = { t: Tree a | balanced t } @-}

{-@ reflect pow2 @-}
{-@ pow2 :: Nat -> Nat @-}
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * pow2 (n - 1)

{-@ reflect log2L @-}
{-@ log2L :: Nat -> Nat @-}
log2L :: Int -> Int
log2L n
  | n > 1     = 1 + log2L (div n 2)
  | otherwise = 0

{-@ reflect ceilLog @-}
{-@ ceilLog :: n : Int -> r : { Int | log2L (n) <= r } @-}
ceilLog :: Int -> Int
ceilLog n
  | n <= 1    = 0
  | pow2 (log2L n) == n = log2L n
  | otherwise = log2L n + 1

{-@ reflect braun @-}
{-@ braun :: Tree a -> Bool @-}
braun :: Tree a -> Bool
braun (Node _ l r) = (nodeCount l == nodeCount r || nodeCount l == (nodeCount r) + 1) && (braun l) && (braun r)
braun Nil = True

{-@ type Array a = { t : Tree a | braun t } @-}
{-@ type ArrayN a N = { arr : Array a | nodeCount arr == N } @-}
{-@ type ArrayNN1 a N = { arr : Array a | nodeCount arr == N  || nodeCount arr == N + 1} @-}
{-@ type ArrayL a N = { arr: Array a | nodeCount arr == N || nodeCount arr == N + 1 } @-}
{-@ type ArrayNE a = { arr : Array a | nodeCount arr > 0 } @-}
{-@ type ArrayGE a N = { arr : Array a | nodeCount arr >= N } @-}
{-@ type ArrayLE a N = { arr : Array a | nodeCount arr <= N } @-}
{-@ type ArrayU a N = { arr : Array a | nodeCount arr >= N || nodeCount arr == N - 1 } @-}

type Array a = Tree a

