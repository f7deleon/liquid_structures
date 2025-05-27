{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module OptimizedOperations where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup)
import BraunTree
import BasicOperations
import Basics
import ImprovedList

{-@ reflect del_hi @-}
{-@ del_hi :: n : Nat -> ArrayN a n -> { a : Array a | n > 0 => nodeCount a == n - 1  } @-}
del_hi :: (Eq a) => Int -> Array a -> Array a
del_hi _ Nil = Nil
del_hi n (Node v l r)
  | n == 1 = Nil
  | not (even n) = makeT v l (del_hi (div n 2) r)
  | otherwise = makeT v (del_hi (div n 2) l) r

{-@ reflect add_lo @-}
{-@ add_lo :: (Eq a) => x : a -> arr : Array a -> ArrayN a { nodeCount arr + 1 } @-}
add_lo :: (Eq a) => a -> Array a -> Array a
add_lo x Nil = singleton x
add_lo x (Node v l r) = makeT x (add_lo v r) l

{-@ reflect del_lo @-}
{-@ del_lo :: arr : Array a -> { arr2 : Array a | nodeCount arr > 0 => nodeCount arr2 == nodeCount arr - 1  } @-}
del_lo :: Array a -> Array a
del_lo Nil = Nil
del_lo (Node _ l r) = merge l r

{-@ reflect merge @-}
{-@ merge :: arr1 : Array a -> { arr2 : Array a | nodeCount arr2 == nodeCount arr1 || nodeCount arr1 == nodeCount arr2 + 1 } -> ArrayN a { nodeCount arr1 + nodeCount arr2 } @-}
merge :: Array a -> Array a -> Array a
merge Nil r = r
merge (Node v l r) rr = Node v rr (merge l r)

{-@ reflect add_hi @-}
{-@ add_hi :: a -> arr : Array a -> ArrayN a { nodeCount arr + 1 } @-}
add_hi :: (Eq a) => a -> Array a -> Array a
add_hi a arr = update (nodeCount arr) a arr

{-@ reflect size_fast @-}
{-@ size_fast :: arr : Array a -> { n : Nat | n == nodeCount arr } @-}
size_fast :: Array a -> Int
size_fast Nil = 0
size_fast (Node _ l r) = 1 + 2 * n + diff n l
  where
    n = size_fast r

{-@ reflect diff @-}
{-@ diff :: n: Nat -> arr : { Array a | nodeCount arr == n || nodeCount arr == n + 1 } -> { nf : Nat | nf == nodeCount arr - n }@-}
diff :: Int -> Array a -> Int
diff _ Nil = 0
diff n (Node _ l r)
  | n == 0 = 1
  | even n  = diff ((div n 2) -1) r
  | otherwise = diff (div n 2) l

{-@ reflect lh @-}
{-@ lh :: arr : Array a -> Nat @-}
lh :: Array a -> Int
lh Nil = 0
lh (Node _ l _) = 1 + lh l

-- {-@ reflect braun2_of @-}
-- {-@ braun2_of :: a -> n : Nat -> (ArrayN a {n + 1}, ArrayN a n) @-}
-- braun2_of :: (Eq a) => a -> Int -> (Array a, Array a)
-- braun2_of x 0 = (singleton x, Nil)
-- braun2_of x n
--   | even n = let (s,t) = braun2_of x (div (n-2) 2) in (makeT x s s, makeT x s t)
--   | otherwise = let (s,t) = braun2_of x (div (n-1) 2) in (makeT x s t, makeT x t t)

-- {-@ reflect braun_of @-}
-- {-@ braun_of :: a -> n: Nat -> ArrayN a n @-}
-- braun_of :: (Eq a) => a -> Int -> Array a
-- braun_of x n = t
--     where
--         (_, t) = (braun2_of x n)

-- {-@ delete_node :: n: { Nat | n > 0 } -> arr : ArrayGE a n -> res : { Array a | nodeCount res == nodeCount arr - 1 } @-}
-- delete_node :: (Eq a) => Int -> Array a -> Array a
-- delete_node 1 (Node v l r) = merge l r
-- delete_node n t@(Node v l r)
--     | (even n) = delete_node_left n t
--     | otherwise = delete_node_right n t

-- {-@ delete_node_left :: n: { Nat | n > 1 && even n } -> arr : ArrayGE a n -> res : { Array a | nodeCount res == nodeCount arr - 1 } @-}
-- delete_node_left :: (Eq a) => Int -> Array a -> Array a
-- delete_node_left n (Node v l r)
--     | nodeCount newLeft == nodeCount r = Node v newLeft r
--     | nodeCount newLeft + 1 == nodeCount r  = delete_node_left_right_great n v newLeft r
--     where
--         newLeft = (delete_node (div n 2) l)

-- {-@ delete_node_left_right_great :: n: { Nat | n > 1 && even n } ->
--             v : a ->
--             l : Array a ->
--             r : { Array a | nodeCount l + 1 == nodeCount r  }  ->
--             res : { Array a | nodeCount res == nodeCount l + nodeCount r + 1 }
--             @-}
-- delete_node_left_right_great :: (Eq a) => Int -> a -> Array a -> Array a -> Array a
-- delete_node_left_right_great n v l r = Node v (add_hi firstRight l) (del_lo r)
--     where
--      firstRight = lookup1 1 r


-- {-@ delete_node_right :: n: { Nat | n > 1 && not (even n) } -> arr : ArrayGE a n -> res : { Array a | nodeCount res == nodeCount arr - 1 } @-}
-- delete_node_right :: (Eq a) => Int -> Array a -> Array a
-- delete_node_right n (Node v l r)
--     | nodeCount newRight == nodeCount l + 1 = Node v l newRight
--     | nodeCount newRight == nodeCount l + 2  = delete_node_right_left_great n v l newRight
--     where
--         newRight = (delete_node (div n 2) r)

-- {-@ delete_node_right_left_great :: n: { Nat | n > 1 && not (even n) } ->
--             v : a ->
--             l : Array a ->
--             r : { Array a | nodeCount l == nodeCount r + 2  }  ->
--             res : { Array a | nodeCount res == nodeCount l + nodeCount r + 1 }
--             @-}
-- delete_node_right_left_great :: (Eq a) => Int -> a -> Array a -> Array a -> Array a
-- delete_node_right_left_great n v l r = Node v (del_hi (nodeCount l) l) (add_lo lastLeft r)
--     where
--     lastLeft = lookup1 (nodeCount l) l
