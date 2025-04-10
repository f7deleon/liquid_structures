{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module BasicOperations where
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup)
import BraunTree
import Basics

{-@ reflect lookup1 @-}
{-@ lookup1 :: { n: Nat | n > 0 } -> ArrayGE a n -> a @-}
lookup1 :: Int -> Array a -> a
lookup1 1 t@(Node v _ _) = v
lookup1 n t@(Node v l r)
  | even n = lookup1 (div n 2) l
  | otherwise = lookup1 (div n 2) r

{-@ reflect singleton @-}
{-@ singleton :: a -> ArrayN a 1 @-}
singleton :: Eq a => a -> Array a
singleton x = Node x Nil Nil

{-@ reflect makeT @-}
{-@ makeT :: v: a -> l : Array a -> r : { Array a | nodeCount l == nodeCount r || nodeCount l == nodeCount r + 1 } -> t : ArrayN a { 1 + nodeCount l + nodeCount r } @-}
makeT :: Eq a => a -> Array a -> Array a -> Array a
makeT v l r = Node v l r

{-@ type ArrayNON1 a N I = { arr : Array a | (I <= N => nodeCount arr == N) && (I == N + 1 => nodeCount arr == N + 1) } @-}

{-@ reflect update1 @-}
{-@ update1 :: { n: Nat | n > 0 } -> a -> arr : ArrayGE a { n - 1 } -> ArrayNON1 a { nodeCount arr } { n } @-}
update1 :: Eq a => Int -> a -> Array a -> Array a
update1 _ x Nil = singleton x
update1 1 x t@(Node v l r) = makeT x l r
update1 n x t@(Node v l r)
  | even n = makeT v (update1 (div n 2) x l) r
  | otherwise = makeT v l (update1 (div (n - 1) 2) x r)

{-@ reflect adds @-}
{-@ adds :: l: [a] -> n : Nat -> ArrayN a n -> ArrayN a { n + len l } @-}
adds :: Eq a => [a] -> Int -> Array a -> Array a
adds [] _ t = t
adds (x:xs) n t = adds xs (n + 1) (update1 (n + 1) x t)

{-@ reflect list @-}
{-@ list :: arr : Array a -> { xs : [a] | nodeCount arr == len xs } @-}
list :: (Eq a) => Array a -> [a]
list Nil = []
list (Node x l r) = x : splice (list l) (list r)

{-@ reflect splice @-}
{-@ splice :: xs: [a] -> ys: [a] -> zs : { [a] | len zs == len xs + len ys }@-}
splice :: (Eq a) => [a] -> [a] -> [a]
splice (x:xs) ys = x : splice ys (xs)
splice [] ys = ys

{-@ reflect  lookup @-}
{-@ lookup :: n: Nat -> ArrayGE a { n + 1 } -> a @-}
lookup :: Int -> Array a -> a
lookup n arr = lookup1 (n + 1) arr

{-@ reflect update @-}
{-@ update :: n: Nat -> a -> arr : ArrayGE a n -> ArrayNON1 a { nodeCount arr } { n + 1 } @-}
update :: Eq a => Int -> a -> Array a -> Array a
update n x arr = update1 (n + 1) x arr

len :: Array a -> Int
len arr = nodeCount arr

{-@ reflect array @-}
{-@ array :: (Eq a) => xs : [a] -> arr : ArrayN a  { len xs } @-}
array :: (Eq a) => [a] -> Array a
array xs = adds xs 0 Nil

