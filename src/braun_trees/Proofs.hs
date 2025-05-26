{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Proofs where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup)
import BraunTree
import BasicOperations
import ImprovedList
import OptimizedOperations
import Basics

{-@ bottom_tree ::  t1 : Array () -> t2 : ArrayN () { nodeCount t1 } -> { t1 == t2 } @-}
bottom_tree :: Tree () -> Tree () -> Proof
bottom_tree Nil Nil = ()
bottom_tree t1@(Node () l r) t2@(Node () l2 r2) = t1 == t2 
              === (Node () l r) == (Node () l2 r2)
              === ((() == ()) && (l == l2) && (r == r2))
              === ((l == l2) && (r == r2)) ? bottom_tree l l2
              === (r == r2) ? bottom_tree r r2
              *** QED
 

{-@ corlary1 :: (Eq a) => { arr : Array a | nodeCount arr > 0 } -> { n : Nat | n > 1 && n < nodeCount arr } -> { not (even n) => ((div n 2) > 1 && (div n 2) < nodeCount (right arr)) && even n => ((div n 2) > 1 && (div n 2) < nodeCount (left arr)) } @-}
corlary1 :: (Eq a) => Array a -> Int -> Proof
corlary1 (Node v l r) n
  | even n = ((div n 2) > 1 && (div n 2) < nodeCount l) *** QED
  | otherwise = ((div n 2) > 1 && (div n 2) < nodeCount r) *** QED

aux :: [a] -> [a] -> Int -> [a]
aux xs ys n
  | even n = xs
  | otherwise = ys
{-@ inline aux @-}


{-@ list_tree_lookup_equallity :: (Eq a) => { xs : [a] | len xs > 0 } -> { ys : [a] | len ys <= len xs && len xs <= len ys + 1 } -> { n : Nat | n < len xs + len ys } -> { lookupL n (splice xs ys) == lookupL (div n 2) (aux xs ys n) } @-}
{-@ ple list_tree_lookup_equallity @-}
list_tree_lookup_equallity :: (Eq a) => [a] -> [a] -> Int -> Proof
list_tree_lookup_equallity [] _ _ = trivial *** QED
list_tree_lookup_equallity (x:xs) ys 0 = lookupL 0 (splice (x:xs) ys) == lookupL (div 0 2) (aux (x:xs) ys 0)
                      === lookupL 0 (x: splice ys xs) == lookupL 0 (x:xs) *** QED
list_tree_lookup_equallity (x:xs) ys n
        | even n = list_tree_lookup_equallity ys xs (n - 1)
        | otherwise = list_tree_lookup_equallity ys xs (n - 1)

{-@ list_array_equality :: arr : { Array a | nodeCount arr > 0 } -> n : { Nat | n < nodeCount arr } -> { lookup n arr == lookupL n (list arr) } @-}
list_array_equality :: (Eq a) => Array a -> Int -> Proof
list_array_equality  arr@(Node v l r) 0 = lookup 0 arr == lookupL 0 (list arr)
                                === v == lookupL 0 (v : (splice (list l ) (list r)))
                                === v == v *** QED
list_array_equality arr@(Node v l r) n
  | even n = lookup n arr == lookupL n (list arr)
              === lookup1 (n + 1) (arr) == lookupL n (v : (splice (list l) (list r)))
              === lookup1 (div n 2) r == lookupL (n - 1) (splice (list l) (list r)) ? list_tree_lookup_equallity (list l) (list r) (n - 1)
              === lookup (div (n - 1) 2) r == lookupL (div (n - 1) 2) (list r) ? list_array_equality r (div (n - 1) 2)
              *** QED
  | otherwise = lookup n arr == lookupL n (list arr)
              === lookup1 (n + 1) arr == lookupL n (v : (splice (list l) (list r)))
              === lookup1 (div (n + 1) 2) l == lookupL (n - 1) (splice (list l) (list r)) ? list_tree_lookup_equallity (list l) (list r) (n -1)
              === lookup (div (n - 1) 2) l == lookupL (div (n - 1) 2) (list l) ? list_array_equality l (div (n - 1) 2)
              *** QED



{-@ reflect append @-}
append :: a -> [a] -> [a]
append x xs = x:xs

{-@ ple listAdd @-}
{-@ listAdd :: (Eq a) => x: a -> arr: Array a -> {  append x (list arr) == list (add_lo x arr) } @-}
listAdd :: (Eq a) => a -> Array a -> Proof
listAdd x Nil = append x (list Nil) == list (add_lo x Nil)
                   === (x:[]) == list (Node x Nil Nil)
                   === (x:[]) == x : (splice (list Nil) (list Nil))
                   === (x:[]) == (x:[])
                   *** QED
listAdd x arr@(Node v l r) = append x (list arr) == list (add_lo x arr)
                === append x (list arr) == list (makeT x (add_lo v r) l)
                === (x:(list arr)) == list (Node x (add_lo v r) l)
                === (x:(list arr)) == x : splice (list (add_lo v r)) (list l) ? listAdd v r
                === (x:(list arr)) == x : splice (append v (list r)) (list l)
                === (x:(list arr)) == x : (v : splice (list l) (list r))
                *** QED

{-@ reflect btail @-}
{-@ btail :: xs : [a] -> ys : { [a] | len xs > 0 => len ys == len xs - 1}@-}
btail :: [a] -> [a]
btail ([]) = []
btail (x:xs) = xs

-- {-@ ple listDel @-}
-- {-@ listDel :: (Eq a) => arr:  Array a -> { btail (list arr) == list (del_lo arr) } @-}
-- listDel :: (Eq a) => Array a -> Proof
-- listDel (Nil) = ()
-- listDel arr@(Node v l r) = btail (list arr) == list (del_lo arr)
--                 === btail (v : (splice (list l) (list r))) == list (merge l r)
--                 === (splice (list l) (list r)) == list (merge l r) ? spliceMergeEq l r
--                 *** QED
