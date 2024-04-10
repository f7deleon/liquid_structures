
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}

module BraunTrees where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, take, drop, repeat, head, tail)
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

{-@ nodeCount :: t : Tree a -> n : Nat @-}
nodeCount :: Tree a -> Int
nodeCount (Node _ l r) = 1 + nodeCount l + nodeCount r
nodeCount Nil = 0
{-@ measure nodeCount @-}

balanced :: Tree a -> Bool
balanced t = height t - minHeight t <= 1
{-@ reflect balanced @-}

{-@ reflect log2f @-}
log2f :: Int -> Int
log2f 0 = 0
log2f 1 = 1
log2f n = 1 + (log2f (div n 2))

{-@ reflect pow2 @-}
pow2 :: Int -> Int
pow2 0 = 1
pow2 n = 2 * (pow2 (n -1))

{-@ reflect log2t @-}
log2t :: Int -> Int
log2t 0 = 0
log2t 1 = 1
log2t n
  | (pow2 lf) > n = lf - 1
  | otherwise = lf
  where
    lf = log2f n

{-@ braun :: Tree a -> Bool @-}
braun :: Tree a -> Bool
braun (Node _ l r) = (nodeCount l == nodeCount r || nodeCount l == (nodeCount r) + 1) && (braun l) && (braun r)
braun Nil = True
{-@ reflect braun @-}

{-@ type Array a = { t : Tree a | braun t } @-}
{-@ type ArrayN a N = { arr : Array a | nodeCount arr = N } @-}
{-@ type ArrayL a N = { arr: Array a | nodeCount arr == N || nodeCount arr == N + 1 } @-}
{-@ type ArrayNE a = { arr : Array a | height arr > 0 } @-}
{-@ type ArrayGE a N = { arr : Array a | nodeCount arr >= N } @-}
{-@ type ArrayLE a N = { arr : Array a | nodeCount arr <= N } @-}
{-@ type ArrayU a N = { arr : Array a | nodeCount arr >= N || nodeCount arr == N - 1 } @-}

{-@ height :: t: Tree a -> i : Nat  @-}
height :: Tree a -> Int
height (Node _ l r) = 1 + max (height l) (height r)
height Nil = 0
{-@ measure height @-}

{-@ minHeight :: Tree a -> Nat @-}
minHeight :: Tree a -> Int
minHeight (Node _ l r) = 1 + min (minHeight l) (minHeight r)
minHeight Nil = 0
{-@ measure minHeight @-}

type Array a = Tree a

{-@ lookup1 :: { n: Nat | n > 0 } -> ArrayGE a n -> a @-}
lookup1 :: Int -> Array a -> a
lookup1 1 t@(Node v _ _) = v
lookup1 n t@(Node v l r)
  | even n = lookup1 (div n 2) l
  | otherwise = lookup1 (div n 2) r
{-@ reflect lookup1 @-}

{-@ singleton :: a -> ArrayN a 1 @-}
{-@ reflect singleton @-}
singleton :: Eq a => a -> Array a
singleton x = Node x Nil Nil

{-@ makeT :: v: a -> l : Array a -> r : { Array a | nodeCount l == nodeCount r || nodeCount l == nodeCount r + 1 } -> t : ArrayN a { 1 + nodeCount l + nodeCount r } @-}
{-@ reflect makeT @-}
makeT :: Eq a => a -> Array a -> Array a -> Array a
makeT v l r = Node v l r

{-@ type ArrayNON1 a N I = { arr : Array a | (I <= N => nodeCount arr == N) && (I == N + 1 => nodeCount arr == N + 1) } @-}
{-@ update1 :: { n: Nat | n > 0 } -> a -> arr : ArrayGE a { n - 1 } -> ArrayNON1 a { nodeCount arr } { n } @-}
update1 :: Eq a => Int -> a -> Array a -> Array a
update1 _ x Nil = singleton x
update1 1 x t@(Node v l r) = makeT x l r
update1 n x t@(Node v l r)
  | even n = makeT v (update1 (div n 2) x l) r
  | otherwise = makeT v l (update1 (div (n - 1) 2) x r)
{-@ reflect update1 @-}

{-@ adds :: l: [a] -> n : Nat -> ArrayN a n -> ArrayN a { n + len l } @-}
adds :: Eq a => [a] -> Int -> Array a -> Array a
adds [] _ t = t
adds (x:xs) n t = adds xs (n + 1) (update1 (n + 1) x t)
{-@ reflect adds @-}

{-@ list :: arr : Array a -> { xs : [a] | nodeCount arr == len xs } @-}
list :: (Eq a) => Array a -> [a]
list Nil = []
list (Node x l r) = x : splice (list l) (list r)
{-@ reflect list @-}

{-@ splice :: xs: [a] -> ys: [a] -> zs : { [a] | len zs == len xs + len ys }@-}
{-@ reflect splice @-}
splice :: (Eq a) => [a] -> [a] -> [a]
splice (x:xs) ys = x : splice ys (xs)
splice [] ys = ys

{-@ lookup2 :: n: Nat -> ArrayGE a { n + 1 } -> a @-}
lookup2 :: Int -> Array a -> a
lookup2 n arr = lookup1 (n + 1) arr
{-@ reflect  lookup2 @-}

{-@ update :: n: Nat -> a -> arr : ArrayGE a n -> ArrayNON1 a { nodeCount arr } { n + 1 } @-}
{-@ reflect update @-}
update :: Eq a => Int -> a -> Array a -> Array a
update n x arr = update1 (n + 1) x arr

len :: Array a -> Int
len arr = nodeCount arr

{-@ array :: (Eq a) => xs : [a] -> arr : ArrayN a  { len xs } @-}
array :: (Eq a) => [a] -> Array a
array xs = adds xs 0 Nil
{-@ reflect array @-}

{-@ corlary1 :: (Eq a) => { arr : Array a | nodeCount arr > 0 } -> { n : Nat | n > 1 && n < nodeCount arr } -> {
     not (even n) => ((div n 2) > 1 && (div n 2) < nodeCount (right arr)) &&
     even n => ((div n 2) > 1 && (div n 2) < nodeCount (left arr))
      } @-}
corlary1 :: (Eq a) => Array a -> Int -> Proof
corlary1 (Node v l r) n
  | even n = ((div n 2) > 1 && (div n 2) < nodeCount l) *** QED
  | otherwise = ((div n 2) > 1 && (div n 2) < nodeCount r) *** QED

aux :: [a] -> [a] -> Int -> [a]
aux xs ys n
  | even n = xs
  | otherwise = ys
{-@ inline aux @-}


{-@ list_tree_lookup_equallity :: (Eq a) => { xs : [a] | len xs > 0 } -> ys : { [a] | len ys <= len xs && len xs <= len ys + 1 } -> n : { Nat | n < len xs + len ys } ->
      { lookupL n (splice xs ys) == lookupL (div n 2) (aux xs ys n) }
      @-}
{-@ ple list_tree_lookup_equallity @-}
list_tree_lookup_equallity :: (Eq a) => [a] -> [a] -> Int -> Proof
list_tree_lookup_equallity [] _ _ = trivial *** QED
list_tree_lookup_equallity (x:xs) ys 0 = lookupL 0 (splice (x:xs) ys) == lookupL (div 0 2) (aux (x:xs) ys 0)
                      === lookupL 0 (x: splice ys xs) == lookupL 0 (x:xs) *** QED
list_tree_lookup_equallity (_:xs) ys n = list_tree_lookup_equallity ys xs (n - 1)


{-@ list_array_equality :: arr : { Array a | nodeCount arr > 0 } -> n : { Nat | n < nodeCount arr } -> { lookup2 n arr == lookupL n (list arr) } @-}
list_array_equality :: (Eq a) => Array a -> Int -> Proof
list_array_equality  arr@(Node v l r) 0 = lookup2 0 arr == lookupL 0 (list arr)
                                === v == lookupL 0 (v : (splice (list l ) (list r)))
                                === v == v *** QED
list_array_equality arr@(Node v l r) n
  | even n = lookup2 n arr == lookupL n (list arr)
              === lookup1 (n + 1) (arr) == lookupL n (v : (splice (list l) (list r)))
              === lookup1 (div n 2) r == lookupL (n - 1) (splice (list l) (list r)) ? list_tree_lookup_equallity (list l) (list r) (n - 1)
              === lookup2 (div (n - 1) 2) r == lookupL (div (n - 1) 2) (list r) ? list_array_equality r (div (n - 1) 2)
              *** QED
  | otherwise = lookup2 n arr == lookupL n (list arr)
              === lookup1 (n + 1) arr == lookupL n (v : (splice (list l) (list r)))
              === lookup1 (div (n + 1) 2) l == lookupL (n - 1) (splice (list l) (list r)) ? list_tree_lookup_equallity (list l) (list r) (n -1)
              === lookup2 (div (n - 1) 2) l == lookupL (div (n - 1) 2) (list l) ? list_array_equality l (div (n - 1) 2)
              *** QED

{-@ del_hi :: n : Nat -> ArrayN a n -> { a : Array a | n > 0 => nodeCount a == n - 1  } @-}
del_hi :: Int -> Array a -> Array a
del_hi _ Nil = Nil
del_hi n (Node v l r)
  | n == 1 = Nil
  | not (even n) = makeT v l (del_hi (div n 2) r)
  | otherwise = makeT v (del_hi (div n 2) l) r

{-@ add_lo :: (Eq a) => x : a -> arr : Array a -> ArrayN a { nodeCount arr + 1 } @-}
{-@ reflect add_lo @-}
add_lo :: (Eq a) => a -> Array a -> Array a
add_lo x Nil = singleton x
add_lo x (Node v l r) = makeT x (add_lo v r) l

{-@ del_lo :: arr : Array a -> { arr2 : Array a | nodeCount arr > 0 => nodeCount arr2 == nodeCount arr - 1  } @-}
{-@ reflect del_lo @-}
del_lo :: Array a -> Array a
del_lo Nil = Nil
del_lo (Node _ l r) = merge l r

{-@ merge :: arr1 : Array a -> { arr2 : Array a | nodeCount arr2 == nodeCount arr1 || nodeCount arr1 == nodeCount arr2 + 1 } -> ArrayN a { nodeCount arr1 + nodeCount arr2 } @-}
{-@ reflect merge @-}
merge :: Array a -> Array a -> Array a
merge Nil r = r
merge (Node v l r) rr = Node v rr (merge l r)

{-@ add_hi :: a -> arr : Array a -> ArrayN a { nodeCount arr + 1 } @-}
add_hi :: (Eq a) => a -> Array a -> Array a
add_hi a arr = update (nodeCount arr) a arr

{-@ size_fast :: arr : Array a -> { n : Nat | n == nodeCount arr } @-}
size_fast :: Array a -> Int
size_fast Nil = 0
size_fast (Node _ l r) = 1 + 2 * n + diff n l
  where
    n = size_fast r

{-@ diff :: n: Nat -> arr : { Array a | nodeCount arr == n || nodeCount arr == n + 1 } -> { nf : Nat | nf == nodeCount arr - n }@-}
diff :: Int -> Array a -> Int
diff _ Nil = 0
diff n (Node _ l r)
  | n == 0 = 1
  | even n  = diff ((div n 2) -1) r
  | otherwise = diff (div n 2) l

{-@ lh :: arr : Array a -> Nat@-}
lh :: Array a -> Int
lh Nil = 0
lh (Node _ l _) = 1 + lh l

{-@ braun2_of :: a -> n : Nat -> (ArrayN a {n + 1}, ArrayN a n) @-}
braun2_of :: (Eq a) => a -> Int -> (Array a, Array a)
braun2_of x 0 = (singleton x, Nil)
braun2_of x n
  | even n = let (s,t) = braun2_of x (div (n-2) 2) in (makeT x s s, makeT x s t)
  | otherwise = let (s,t) = braun2_of x (div (n-1) 2) in (makeT x s t, makeT x t t)

{-@ braun_of :: a -> n: Nat -> ArrayN a n @-}
braun_of :: (Eq a) => a -> Int -> Array a
braun_of x n = snd (braun2_of x n)
