{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module OptimizedOperationsProof where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup,dropLast,concat)
import BraunTree
import BasicOperations
import ImprovedList
import OptimizedOperations
import Basics

{-@ reflect append @-}
append :: a -> [a] -> [a]
append x xs = x:xs

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

{-@ splice_merge_eq :: arr1 : Array a -> arr2 : {Array a  | nodeCount arr2 == nodeCount arr1 || nodeCount arr1 == nodeCount arr2 + 1 } -> { (splice (list arr1) (list arr2)) == list (merge arr1 arr2) }  @-}
splice_merge_eq :: (Eq a) => Array a -> Array a -> Proof
splice_merge_eq (Nil) (Nil) = () 
splice_merge_eq arr@(Node v l r) (Nil) = (splice (list arr) (list Nil)) == list (merge arr Nil)
                === v : (splice ([]) (splice (list l) (list r))) == list (Node v Nil (merge l r)) 
                === v : (splice ([]) (splice (list l) (list r))) == v : (splice ([])  (list (merge l r))) 
                === splice (list l) (list r) == list (merge l r) ? splice_merge_eq l r
                *** QED
splice_merge_eq arr1@(Node lv ll lr) arr2@(Node rv rl rr) = (splice (list arr1) (list arr2)) == list (merge arr1 arr2) 
               === lv : (splice (list arr2) (splice (list ll) (list lr))) == list (Node lv arr2 (merge ll lr)) 
               === lv : (splice (list arr2) (splice (list ll) (list lr))) == lv : (splice (list arr2) (list (merge ll lr)))
               === (splice (list arr2) (splice (list ll) (list lr))) == (splice (list arr2) (list (merge ll lr))) ? splice_merge_eq ll lr
               *** QED


{-@ listDel :: (Eq a) => arr:  Array a -> { btail (list arr) == list (del_lo arr) } @-}
listDel :: (Eq a) => Array a -> Proof
listDel (Nil) = ()
listDel arr@(Node v l r) = btail (list arr) == list (del_lo arr)
                === btail (v : (splice (list l) (list r))) == list (merge l r)
                === (splice (list l) (list r)) == list (merge l r) ? splice_merge_eq l r
                *** QED

{-@ reflect dropLast @-}
{-@ dropLast :: xs : { [a] | len xs > 0 } -> ys : { [a] | len ys == len xs - 1}@-}
dropLast :: (Eq a) => [a] -> [a]
dropLast [] = []
dropLast (x:xs) 
  | length2 xs == 0 = []
  | otherwise = x : dropLast xs

{-@ dropLastC :: arr : [a] -> { arr2:  [a] | len arr == len arr2 + 1 } -> { (dropLast (splice (arr) (arr2))) == (splice (dropLast arr) (arr2))} @-}
dropLastC :: (Eq a) => [a] -> [a] -> Proof
dropLastC (x:xs) ([]) = ()
dropLastC l@(x:xs) r@(y:ys) = (dropLast (splice l r)) == (splice (dropLast l) r)
                                === dropLast (splice r xs) == (splice r (dropLast xs)) ? dropLastC2 r xs 
                                *** QED

{-@ dropLastC2 :: arr : [a] -> { arr2:  [a] | len arr == len arr2 } -> { (dropLast (splice (arr) (arr2))) == (splice (arr) (dropLast arr2))} @-}
dropLastC2 :: (Eq a) => [a] -> [a] -> Proof
dropLastC2 ([]) ([]) = ()
dropLastC2 l@(x:xs) r@(y:ys) = (dropLast (splice l r)) == (splice l (dropLast r))
                                === dropLast (splice r xs) == (splice (dropLast r) xs) ? dropLastC r xs 
                                *** QED

{-@ listDelHigh :: arr:  { Array a | nodeCount arr > 0 } -> { dropLast (list arr) == list (del_hi (nodeCount arr) arr) } @-}
listDelHigh :: (Eq a) => Array a -> Proof
listDelHigh arr@(Node v Nil Nil) = ()
listDelHigh arr@(Node v l r) 
  | even n = dropLast (list arr) == list (del_hi n arr)
                === v : (dropLast (splice (list l) (list r))) == list (Node v (del_hi (div n 2) l) r)
                === v : (dropLast (splice (list l) (list r))) == v : (splice (list (del_hi (div n 2) l)) (list r))
                === (dropLast (splice (list l) (list r))) == (splice (list (del_hi (div n 2) l)) (list r)) ? listDelHigh l
                === (dropLast (splice (list l) (list r))) == (splice (dropLast (list l)) (list r)) ? dropLastC (list l) (list r)
                *** QED
  | otherwise = dropLast (list arr) == list (del_hi (nodeCount arr) arr)
                === v : (dropLast (splice (list l) (list r))) == list (Node v l (del_hi (div n 2) r))
                === v : (dropLast (splice (list l) (list r))) == v : (splice  (list l) (list (del_hi (div n 2) r)))
                === (dropLast (splice (list l) (list r))) == (splice (list l) (list (del_hi (div n 2) r))) ? listDelHigh r
                === (dropLast (splice (list l) (list r))) == (splice (list l) (dropLast (list r))) ? dropLastC2 (list l) (list r)
                *** QED
  where
    n = nodeCount arr