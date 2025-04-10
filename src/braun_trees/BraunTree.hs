{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module BraunTree where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup)
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

{-@ reflect height @-}
{-@ height :: t: Tree a -> i : { Nat | i >= minHeight t }  @-}
height :: Tree a -> Int
height (Node _ l r) = 1 + max (height l) (height r)
height Nil = 0

{-@ measure minHeight @-}
{-@ minHeight :: t : Tree a -> Nat @-}
minHeight :: Tree a -> Int
minHeight (Node _ l r) = 1 + min (minHeight l) (minHeight r)
minHeight Nil = 0

{-@ reflect balanced @-}
balanced :: Tree a -> Bool
balanced t = height t - minHeight t <= 1 

{-@ reflect log2L @-}
log2L :: Int -> Int 
log2L n
  | n > 1 = 1 + log2L(div n 2)
  | otherwise =  0

{-@ reflect log2H @-}
log2H :: Int -> Int
log2H n
  | n < 1 = 0
  | pow 2 low == n = low
  | otherwise = low + 1
  where
    low = log2L n

{-@ reflect pow @-}
pow :: Int -> Int -> Int
pow _ 0 = 1
pow p n = p* (pow p (n - 1))

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

