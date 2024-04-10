
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}

module ArrayXS where
import Language.Haskell.Liquid.ProofCombinators
import BraunTrees
import Prelude hiding (even, abs, max, min, exponent, lookup, take, drop, repeat, head, tail)
import ImprovedList

{-@ type ArrayXS a XS = { arr : Array a | list arr == XS } @-}

{-@ reflect append @-}
append :: a -> [a] -> [a]
append x xs = x:xs

{-@ merge_add_lo :: (Eq a) => x: a -> l : Array a -> r : { Array a | nodeCount r == nodeCount l || nodeCount r + 1 == nodeCount l }-> t : { ArrayNE a | t == Node x l r } -> { merge (add_lo x r) l == t } @-}
{-@ ple merge_add_lo @-}
merge_add_lo :: (Eq a) => a -> Array a -> Array a -> Array a -> Proof
merge_add_lo x l r@(Nil) t = merge (add_lo x r) l == t
                        === merge (singleton x) l == Node x l Nil
                        === merge (Node x Nil Nil) l == Node x l Nil
                        === Node x l (merge Nil Nil) == Node x l Nil
                        === Node x l Nil == Node x l Nil
                        *** QED
merge_add_lo x l r@(Node vr lr rr) _ =  merge (add_lo x r) l == Node x l r
                  === merge (Node x (add_lo vr rr) lr) l == Node x l r
                  === Node x l (merge (add_lo vr rr) lr) == Node x l r  ? merge_add_lo vr lr rr r
                  *** QED

{-@ add_del_lo :: (Eq a) => x:a -> arr : Array a -> { arr == del_lo (add_lo x arr) }@-}
{-@ ple add_del_lo @-}
add_del_lo :: (Eq a) => a -> Array a -> Proof
add_del_lo x arr@(Nil) = arr == (del_lo (add_lo x arr))
                === arr == (del_lo (Node x Nil Nil))
                === arr == (merge Nil Nil)
                === arr == Nil
                *** QED
add_del_lo x arr@(Node v l r) = arr == del_lo (add_lo x arr)
                === arr == del_lo (makeT x (add_lo v r) l)
                === arr == del_lo (Node x (add_lo v r) l)
                === arr == merge (add_lo v r) l ? merge_add_lo v l r arr
                *** QED


{-@ add_lo_merge :: (Eq a) => x: a -> l : Array a -> r : { Array a | nodeCount r == nodeCount l || nodeCount r + 1 == nodeCount l }-> t : { ArrayNE a | t == Node x l r } -> { add_lo x (merge l r) == t } @-}
{-@ ple add_lo_merge @-}
add_lo_merge :: (Eq a) => a -> Array a -> Array a -> Array a -> Proof
add_lo_merge x l@(Nil) r@(Nil) t = add_lo x (merge l r) == t
                        === add_lo x (merge Nil Nil) == (Node x Nil Nil)
                        === singleton x == (Node x Nil Nil)
                        === (Node x Nil Nil) == (Node x Nil Nil)
                        *** QED
add_lo_merge x l@(Node vl ll rl) r _ =  add_lo x (merge l r) == Node x l r
                  === add_lo x (merge l r) == Node x l r
                  === add_lo x (merge (Node vl ll rl) r) == Node x l r
                  === add_lo x (Node vl r (merge ll rl)) == Node x l r
                  === Node x (add_lo vl (merge ll rl)) r == Node x l r ? add_lo_merge vl ll rl l
                  *** QED


{-@ ple del_add_lo @-}
{-@ del_add_lo :: (Eq a) => arr : ArrayNE a -> x : { a | isValue arr x } -> { arr == add_lo x (del_lo arr) }@-}
del_add_lo :: (Eq a) => Array a -> a -> Proof
del_add_lo arr@(Node v l r) x = arr == add_lo x (del_lo arr)
                === arr == add_lo x (del_lo (Node v l r))
                === arr == add_lo x (merge l r) ? add_lo_merge x l r arr
                *** QED



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

-- {-@ create :: (Eq a) => xs : [a] -> Array a @-}
-- {-@ reflect create @-}
-- create :: (Eq a) => [a] -> Array a
-- create [] = Nil
-- create (x:xs) = add_lo x (create xs)

-- {-@ create_to_list  :: (Eq a) => xs: [a] -> { list (create xs) == xs } @-}
-- create_to_list :: (Eq a) => [a] -> Proof
-- create_to_list xs@([]) = list (create xs) == xs
--                     === list Nil == xs
--                     === [] == xs
--                     *** QED
-- create_to_list (x:xs) = list (create (x:xs)) == (x:xs)
--                       === list (add_lo x (create xs)) == (x:xs) ? listAdd x (create xs)
--                       === append x (list (create xs)) == (x:xs) ? create_to_list xs
--                       *** QED

{-
{-@ cr :: ArrayXS Int [1,2,3,4] @-}
cr = create [1,2,3,4]
-}
{-
{-@ create' :: (Eq a) => xs: [a] -> ArrayXS a xs @-}
create' :: (Eq a) => [a] -> Array a
create' xs = create xs
-}

{-
{-@ listAdds1 :: (Eq a) => x:a -> xs : [a] -> arr : ArrayXS a xs -> { (append x xs) == list (add_lo x arr) } @-}
listAdds1 :: (Eq a) => a -> [a] -> Array a -> Proof
listAdds1 x [] Nil = append x [] == list (add_lo x Nil)
                     === (x:[]) == list (singleton x)
                     === (x:[]) == list (Node x Nil Nil)
                     === (x:[]) == x : (splice (list Nil) (list Nil))
                     === (x:[]) == (x:[])
                     *** QED
listAdds1 x ys arr@(Node v l r)
  | r == Nil = append x (ys) == list (add_lo x arr)
                === (x:ys) == list (makeT x (add_lo v r) l)
                === (x:ys) == list (Node x (add_lo v r) l)
                === (x:ys) == x : (splice (list (add_lo v Nil)) (list l))
                === (x:ys) == x : (splice (list (singleton v)) (list l))
                === (x:ys) == x : (v : splice (list l) (list Nil))
                === (x:ys) == x : (list arr)
                === (x:ys) == (x:ys)
                *** QED
-}
