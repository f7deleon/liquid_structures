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
import Basics

{-@ bottom_tree ::  t1 : Tree () -> t2 : { Tree () | nodeCount t1 == nodeCount t2 } -> { t1 == t2 } @-}
bottom_tree :: Tree () -> Tree () -> Proof
bottom_tree _ _ = ()


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

