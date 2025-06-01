{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Proofs where
import Language.Haskell.Liquid.ProofCombinators
<<<<<<< Updated upstream
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup,dropLast)
=======
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup,concat2)
>>>>>>> Stashed changes
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

-- {-@ spliceChangeC :: arr : [a] -> { arr2:  [a] | len arr >= len arr2 } -> v : a -> n :{ Nat | n < len arr + len arr2 && not (even n) } -> { (splice (change (div n 2) v (arr)) (arr2)) == (change (n -1) v (splice (arr) (arr2))) } @-}
-- spliceChangeC :: (Eq a) => [a] -> [a] -> a -> Int -> Proof
-- spliceChangeC (x:xs) (y:ys) v 1 = ()
-- spliceChangeC l@(x:xs) r@(y:ys) v n = (splice (change (div n 2) v (l)) (r))  ==  (change (n -1) v (splice (l) (r))) 
--                                 === (splice r (change ((div n 2) -1) v xs)) == (change (n -2) v (splice r xs)) ? spliceChangeC2 r xs v (n - 1) 
--                                 *** QED

-- {-@ spliceChangeC2 :: arr : [a] -> { arr2:  [a] | len arr >= len arr2 }  -> v : a -> n :{ Nat | n < len arr + len arr2 && (even n) } -> {  (splice (arr) (change (div n 2) v (arr2)))  ==  (change (n -1) v (splice (arr) (arr2)))  } @-}
-- spliceChangeC2 :: (Eq a) => [a] -> [a] -> a -> Int -> Proof
-- spliceChangeC2 (x:xs) (y:ys) v 0 = ()
-- spliceChangeC2 l@(x:xs) r@(y:ys) v n =  (splice l (change (div n 2) v r))  ==  (change (n -1) v (splice l r)) 
--                                 === (splice (change (div n 2) v r) xs) == (change (n -2) v (splice r xs)) ? spliceChangeC r xs v (n - 1)
--                                 *** QED

-- {-@ update_list_equal :: v : a -> n : Nat -> arr : ArrayGE a n -> { list (update1 n v arr) == change n v (list arr) } @-}
-- update_list_equal :: a -> Int -> Array a ->  Proof
-- update_list_equal v 0 arr = ()
-- update_list_equal v n arr@(Node x l r) 
--   | even n = list (update1 n v arr)  == change n v (list arr)
--             === list (Node x (update1 (div n 2) v l) r)  == x : (change (n -1) v (splice (list l) (list r)))
--             === x: (splice (list (update1 (div n 2) v l)) (list r))  ==  x : (change (n -1) v (splice (list l) (list r))) ? update_list_equal v (div n 2) l
--             === (splice (change (div n 2) v (list l)) (list r))  ==  (change (n -1) v (splice (list l) (list r))) 
--             *** QED
--   | otherwise = list (update1 n v arr)  == change n v (list arr)
--             === list (Node x l  (update1 (div n 2) v r))  == x : (change (n -1) v (splice (list l) (list r)))
--             === x: (splice (list l) (list (update1 (div n 2) v r)))  ==  x : (change (n -1) v (splice (list l) (list r))) ? update_list_equal v (div n 2) r
--             === (splice (list l) (change (div n 2) v (list r)))  ==  (change (n -1) v (splice (list l) (list r))) 
--             *** QED

aux :: [a] -> [a] -> Int -> [a]
aux xs ys n
  | even n = xs
  | otherwise = ys
{-@ inline aux @-}


{-@ list_tree_lookup_equallity :: (Eq a) => { xs : [a] | len xs > 0 } -> { ys : [a] | len ys <= len xs && len xs <= len ys + 1 } -> { n : Nat | n < len xs + len ys } -> { lookupL n (splice xs ys) == lookupL (div n 2) (aux xs ys n) } @-}
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
splice_merge_eq :: Array a -> Array a -> Proof
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
-- {-@ ple listDel @-}
-- {-@ listDel :: (Eq a) => arr:  Array a -> { btail (list arr) == list (del_lo arr) } @-}
-- listDel :: (Eq a) => Array a -> Proof
-- listDel (Nil) = ()
-- listDel arr@(Node v l r) = btail (list arr) == list (del_lo arr)
--                 === btail (v : (splice (list l) (list r))) == list (merge l r)
--                 === (splice (list l) (list r)) == list (merge l r) ? spliceMergeEq l r
--                 *** QED

-- {-@ updateAdd :: arr: Array a -> x : a -> { list (update1 (nodeCount arr + 1) x arr) == concat2 (list (arr)) x } @-} 
-- updateAdd ::(Eq a) => Array a -> a -> Proof
-- updateAdd Nil v = list (update1 (1) v Nil) == concat2 (list (Nil)) v 
--                 === ([v] == [v]) *** QED
-- updateAdd t@(Node v  Nil Nil) x = list (update1 (2) x t) == concat2 (list (t)) x 
--                 === list (Node v (Node x Nil Nil) Nil) == concat2 [v] x
--                 === v : x : [] == v : x : []
--                 *** QED
-- updateAdd t@(Node v l r) x 
--     | even n = list (Node v (update1 (div n 2) x l) r) == concat2 (list (t)) x 
--               === v : (splice (list (update1 (div n 2) x l)) (list r)) == v : (concat2 (splice (list l) (list r)) x) ? updateAdd l x
--               === v : (splice (concat2 (list l) x) (list r)) == v : (concat2 (splice (list l) (list r)) x) ? concat2Splice x (list l) (list r)
--               *** QED
--     | otherwise = list (Node v l (update1 (div n 2) x r)) == concat2 (list (t)) x
--             === v : (splice (list l) (list (update1 (div n 2) x r))) == v : (concat2 (splice (list l) (list r)) x) ? updateAdd r x
--             === v : splice (list l) (concat2 (list r) x) == v : (concat2 (splice (list l) (list r)) x) ? concat2Splice2 x (list l) (list r)
--             *** QED
--     where 
--       n = nodeCount t + 1

-- {-@ concat2Splice :: v: a -> xs : [a] -> ys : { [a] | length2 xs == length2 ys + 1 } -> { concat2 (splice xs ys) v == splice (concat2 xs v) ys } @-}
-- concat2Splice ::(Eq a) => a -> [a] -> [a] -> Proof
-- concat2Splice v (x:[]) ([]) = concat2 (splice [x] []) v == splice (concat2 [x] v) []
--                               === x:v:[] == x:v:[]
--                               ***QED                          
-- concat2Splice v l1@(x:xs) l2@(y:ys) = concat2 (splice l1 l2) v == splice (concat2 l1 v) l2 
--                               === (concat2 (splice l2 xs) v) == (splice l2 (concat2 xs v)) ? concat2Splice2 v l2 xs
--                               *** QED

-- {-@ concat2Splice2 :: v: a -> xs : [a] -> ys : { [a] | length2 xs == length2 ys } -> { concat2 (splice xs ys) v == splice xs (concat2 ys v) } @-}
-- concat2Splice2 :: (Eq a) => a -> [a] -> [a] -> Proof
-- concat2Splice2 v ([]) ([]) = concat2 (splice [] []) v == splice [] (concat2 [] v)
--                               === concat2 (splice [] []) v == splice [] (concat2 [] v) 
--                               === v:[] == v:[]
--                               *** QED
-- concat2Splice2 v l1@(x:xs) l2@(y:ys) = concat2 (splice l1 l2) v == splice l1 (concat2 l2 v) 
--                               === (concat2 (splice l2 xs) v) == (splice (concat2 l2 v) xs) ? concat2Splice v l2 xs
--                               *** QED
