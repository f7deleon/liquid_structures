{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Proofs where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail, lookup,dropLast,concat)
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

{-@ concatSplice ::xs : [a] -> ys : { [a] | len xs == len ys } -> v: [a] -> { concat (splice xs ys) v == splice (concat xs v) ys } @-}
concatSplice ::(Eq a) => [a] -> [a] -> [a] -> Proof
concatSplice ([]) ([]) v@([]) = concat (splice [] []) v == splice (concat [] []) v
                              === concat [] v == splice (concat [] []) v
                              === v == v
                              *** QED
concatSplice ([]) ([]) v@(z:zs) = concat (splice [] []) v == splice (concat [] v) []
                              === concat [] v == splice (concat [] v) []
                              === v == z : (splice [] (zs))
                              === v == z:zs
                              === z:zs == z:zs
                              *** QED
concatSplice (x:xs) (y:ys) v = concat (splice (x:xs) (y:ys)) v == splice (concat (x:xs) v) (y:ys) 
                              === (concat (splice (y:ys) xs) v) == (splice (y:ys) (concat xs v)) ? concatSplice2 (y:ys) xs v
                              *** QED

{-@ concatSplice2 :: xs : [a] -> ys : { [a] | len xs == len ys + 1 } -> v: [a]-> { concat (splice xs ys) v == splice xs (concat ys v) } @-}
concatSplice2 :: (Eq a) => [a] -> [a] -> [a] -> Proof
concatSplice2 (x:[]) ([]) ([]) = concat (splice [x] []) [] == splice [x] (concat [] []) 
                              === x:[] == x:[]
                              ***QED 
concatSplice2 (x:[]) ([]) v@(z:zs) = concat (splice [x] []) v == splice [x] (concat [] v) 
                              === x:v == x:v
                              ***QED 
concatSplice2 (x:xs) (y:ys) v = concat (splice (x:xs) (y:ys)) v == splice (x:xs) (concat (y:ys) v) 
                              === (concat (splice (y:ys) xs) v) == (splice (concat (y:ys) v) xs) ? concatSplice (y:ys) xs v
                              *** QED
{-@ updateAdd :: arr: Array a -> x : a -> { list (update1 (nodeCount arr + 1) x arr) == concat (list arr) [x] } @-} 
updateAdd ::(Eq a) => Array a -> a -> Proof
updateAdd Nil v = list (update1 1 v Nil) == concat (list (Nil)) [v] 
            === list (Node v Nil Nil) == concat ([]) [v]
            === v : (splice (list Nil) (list Nil)) == v : []
            === v : (splice [] []) == [v]
            === [v] == [v] 
            *** QED
updateAdd t@(Node v l r) x 
    | even (n + 1) = list (update1 (n + 1) x t) == concat (list t) [x] 
            === list (Node v (update1 (div (n + 1) 2) x l) r) == concat (list t) [x]
            === (splice (list (update1 (div (n + 1) 2) x l)) (list r)) == (concat (splice (list l) (list r)) [x]) ? updateAdd l x
            === (splice (concat (list l) [x]) (list r)) == (concat (splice (list l) (list r)) [x]) ? concatSplice (list l) (list r) [x]
            === (concat (splice (list l) (list r)) [x]) == (concat (splice (list l) (list r)) [x])
            *** QED
    | otherwise = list (update1 (n + 1) x t) == concat (list t) [x]
            === list (Node v l (update1 (div (n + 1) 2) x r)) == concat (list (t)) [x]
            === (splice (list l) (list (update1 (div (n + 1) 2) x r))) == (concat (splice (list l) (list r)) [x]) ? updateAdd r x
            === (splice (list l) (concat (list r) [x])) == (concat (splice (list l) (list r)) [x]) ? concatSplice2 (list l) (list r) [x]
            === (concat (splice (list l) (list r)) [x]) == (concat (splice (list l) (list r)) [x])
            *** QED
    where 
      n = nodeCount t


{-@ concatEmpty :: xs : [a] -> ys : {[a] | len ys == 0 } -> { concat xs ys == xs } @-}
concatEmpty :: (Eq a) => [a] -> [a] -> Proof
concatEmpty ([]) ([]) = ()
concatEmpty (x:xs) ys = concat (x:xs) ys == (x:xs)
                        ===  x : (concat xs ys) == (x:xs) ? concatEmpty xs ys
                        === x:xs == x:xs
                        *** QED
{-@ concatOneElement :: xs: [a] -> y:a -> ys:[a] -> { concat (concat xs [y]) ys == concat xs (concat [y] ys) }@-}
concatOneElement :: (Eq a) => [a] -> a -> [a] -> Proof
concatOneElement ([]) v ([]) = ()
concatOneElement (x:xs) v ([]) = concat (concat (x:xs) [v]) ([]) == concat (x:xs) (concat [v] [])
                        === x: (concat (concat xs [v]) ([])) == x : concat xs ([v]) ? concatOneElement xs v ([])
                        === x : (concat xs (concat [v] [])) == x : concat xs ([v])
                        === x : (concat xs [v]) == x : concat xs [v]
                        *** QED
concatOneElement ([]) v (y:ys) = concat (concat [] [v]) (y:ys) == concat [] (concat [v] (y:ys))
                        === concat [v] (y:ys) == concat [] (v:y:ys)
                        === (v:y:ys) == (v:y:ys)
                        *** QED
concatOneElement (x:xs) v (y:ys) = concat (concat (x:xs) [v]) (y:ys) == concat (x:xs) (concat [v] (y:ys))
                        === x : (concat (concat (xs) [v]) (y:ys)) == x: (concat xs (v:y:ys)) ? concatOneElement xs v (y:ys)
                        *** QED

{-@ updateAddList :: arr: Array a -> xs : [a] -> { list (adds xs (nodeCount arr) arr) == concat (list arr) xs } @-} 
updateAddList ::(Eq a) => Array a -> [a] -> Proof
updateAddList arr@(Nil) xs@([]) = ()
updateAddList arr@(Node v l r) xs@([]) = list (adds [] (nodeCount arr) arr) == concat (list arr) xs
                                === list arr == concat (list arr) xs ? concatEmpty (list arr) xs
                                *** QED
updateAddList arr@(Nil) xs@(l:ls) = list (adds xs (nodeCount arr) arr) == concat (list arr) xs 
            === list (adds xs (0) Nil) == concat (list Nil) xs 
            === list (adds xs (0) Nil) == xs
            === list (adds ls 1 (Node l Nil Nil)) == xs ? updateAddList (Node l Nil Nil) ls
            === concat (list (Node l Nil Nil)) ls == xs
            === concat [l] ls == xs 
            === xs == xs
            *** QED
updateAddList t@(Node v l r) ls@(x:xs) = list (adds ls n t) == concat (list t) ls
            === list (adds xs (n + 1) (update1 (n + 1) x t)) == concat (list (t)) ls ? updateAddList (update1 (n + 1) x t) xs
            === (concat (list (update1 (n + 1) x t)) xs) == concat (list (t)) ls ? updateAdd t x
            === concat (concat (list t) [x]) xs == concat (list (t)) (x:xs) ? concatOneElement (list t) x xs
            *** QED
    where 
      n = nodeCount t

-- {-@ update_list_equal :: v : a -> n : { Nat | n >= 1 } -> arr : ArrayGE a n -> { list (update1 n v arr) == change (n-1) v (list arr) } @-}
-- update_list_equal :: (Eq a) => a -> Int -> Array a ->  Proof
-- update_list_equal v 1 arr@(Node x l r) = list (update1 1 v arr) == change 0 v (list arr)
--                         === list (Node v l r) == v : (splice (list l) (list r))
--                         === v : (splice (list l) (list r)) == v : (splice (list l) (list r))
--                         *** QED
-- update_list_equal v n arr@(Node x l r) 
--   | even n = list (update1 n v arr)  == change n v (list arr)
--             === list (Node x (update1 (div n 2) v l) r)  == x : (change (n -1) v (splice (list l) (list r)))
--             === x: (splice (list (update1 (div n 2) v l)) (list r))  ==  x : (change (n -1) v (splice (list l) (list r))) ? update_list_equal v (div n 2) l
--             === (splice (change (div n 2) v (list l)) (list r))  ==  (change (n -1) v (splice (list l) (list r))) ? spliceChangeC (list l) (list r) v n
--             *** QED
--   | otherwise = list (update1 n v arr)  == change n v (list arr)
--             === list (Node x l  (update1 (div n 2) v r))  == x : (change (n -1) v (splice (list l) (list r)))
--             === x: (splice (list l) (list (update1 (div n 2) v r)))  ==  x : (change (n -1) v (splice (list l) (list r))) ? update_list_equal v (div n 2) r
--             === (splice (list l) (change (div n 2) v (list r)))  ==  (change (n -1) v (splice (list l) (list r))) 
--             *** QED


-- {-@ spliceChangeC :: arr : [a] -> { arr2:  [a] | len arr >= len arr2 } -> v : a -> n :{ Nat | n >= 1 && n < len arr + len arr2 && (even n) } -> { (splice (change (div n 2) v (arr)) (arr2)) == (change (n -1) v (splice (arr) (arr2))) } @-}
-- spliceChangeC :: (Eq a) => [a] -> [a] -> a -> Int -> Proof
-- spliceChangeC (x:xs) (y:ys) v 1 = ()
-- spliceChangeC l@(x:xs) r@(y:ys) v n = (splice (change (div n 2) v (l)) (r))  ==  (change (n -1) v (splice (l) (r))) 
--                                 === (splice r (change ((div n 2) -1) v xs)) == (change (n -2) v (splice r xs)) ? spliceChangeC2 r xs v (n - 1) 
--                                 *** QED

-- {-@ spliceChangeC2 :: arr : [a] -> { arr2:  [a] | len arr >= len arr2 }  -> v : a -> n :{ Nat |  n >= 1 && n < len arr + len arr2 && not (even n) } -> {  (splice (arr) (change (div n 2) v (arr2)))  ==  (change (n -1) v (splice (arr) (arr2)))  } @-}
-- spliceChangeC2 :: (Eq a) => [a] -> [a] -> a -> Int -> Proof
-- spliceChangeC2 l@(x:xs) r@(y:ys) v n =  (splice l (change (div n 2) v r))  == (change (n -1) v (splice l r)) 
--                                 === (splice (change (div n 2) v r) xs) == (change (n -2) v (splice r xs)) ? spliceChangeC r xs v (n - 1)
--                                 *** QED