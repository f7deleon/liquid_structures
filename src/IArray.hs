
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}

module IArray where
import Prelude hiding (even, abs, max, min, exponent, lookup, take, drop, repeat, head, tail, concat)
import IRow
import BraunTrees
import ImprovedList

data IArray a where
  IArray :: (Eq a) => Int -> Int -> [Array a] -> [Array a] -> Int -> IArray a

{-@ sizeIArray :: (Eq a) => IArray a -> Int @-}
sizeIArray :: (Eq a) => IArray a -> Int
sizeIArray (IArray _ _ xs ys _) = length2 xs + length2 ys
{-@ measure sizeIArray @-}

{-@
data IArray a where
  IArray :: (Eq a) => { nc : Nat | nc > 0 } -> n : { Nat | n > 0 } -> xs : ListN (ArrayN a nc) n -> ys : List (ArrayN a { nc - 1 }) -> {l : Nat | l == len xs + len ys} -> IArray a
@-}

countNodesArr :: (Eq a) => IArray a -> Int
countNodesArr (IArray nc index xs ys k) = index * nc + (k - index) * (nc - 1)
{-@ measure countNodesArr @-}

indx :: (Eq a) => IArray a -> Int
indx (IArray nc index xs ys k) = index
{-@ measure indx @-}

getK :: (Eq a) => IArray a -> Int
getK (IArray nc index xs ys k) = k
{-@ measure getK @-}

{-@ build :: (Eq a) => t: IRow a -> { iarr : IArray a | sizeIArray iarr == size t && countNodesArr iarr == countRowNodes t } @-}
build :: (Eq a) => IRow a -> IArray a
build (Last k xs) = IArray 1 len2 (map singleton xs) (compleate rest (Nil) []) k
  where
    len2 = length2 xs
    rest = (k - len2)
build (IRow k xs next)
  | index > k = buildkg k iarr xs
  | index == k = buildke k iarr xs
  | index < k = buildkl k iarr xs
  where
    iarr@(IArray nc index narrayl narrayr _) = build next

{-@ type IArrayGK a NK = { arr : IArray a | indx arr > NK && getK iarr == 2 * NK } @-}
{-@ type IArrayEK a NK = { arr : IArray a | indx arr == NK && getK iarr == 2 * NK } @-}
{-@ type IArrayLK a NK = { arr : IArray a | indx arr < NK && getK iarr == 2 * NK } @-}
{-@ type IArrayNKN a NK N = { arr : IArray a | sizeIArray arr == NK && countNodesArr arr == N } @-}

{-@ buildkg :: (Eq a) => nk : Nat -> iarr : IArrayGK a nk  -> rs: { [a] | len rs == nk } -> IArrayNKN a { nk } { len rs + countNodesArr iarr } @-}
{-@ reflect buildkg @-}
buildkg :: (Eq a) => Int -> IArray a -> [a] -> IArray a
buildkg k (IArray nc index ys zs _) xs = IArray (1 + 2* nc) splitindex (makeT3 nc nc xs1 an3 an2) (makeT3 nc (nc - 1) xs2 an4 zs) k
  where
    (xs1, xs2) = split splitindex xs
    (an, an2) = split k ys
    (an3, an4) = split splitindex an
    splitindex = index - k

{-@ buildke :: (Eq a) => nk: Nat  -> iarr : IArrayEK a nk -> rs:{ [a] | len rs == nk } -> IArrayNKN a { nk } { len rs + countNodesArr iarr }  @-}
{-@ reflect buildke @-}
buildke :: (Eq a) => Int -> IArray a -> [a] -> IArray a
buildke k (IArray nc index ys zs _) xs = IArray (2 * nc) k (makeT3 nc (nc -1) xs ys zs) [] k

{-@ buildkl :: (Eq a) => nk: Nat -> iarr: IArrayLK a nk -> rs:{ [a] | len rs == nk } -> IArrayNKN a { nk } { len rs + countNodesArr iarr } @-}
{-@ reflect buildkl @-}
buildkl :: (Eq a) => Int -> IArray a -> [a] -> IArray a
buildkl k (IArray nc index ys zs _) xs = IArray (2* nc) index (makeT3 nc (nc - 1) xs1 ys an3) (makeT3 (nc - 1) (nc - 1) xs2 an an4) k
  where
    (xs1, xs2) = split index xs
    (an, an2) = split (k - index) zs
    (an3, an4) = split index an2

{-@ type SOL N = { n : Nat | n == N || n == N - 1 } @-}
{-@ makeT3 :: (Eq a) => nc1 : Nat -> nc2 : SOL nc1 -> xs : [a] -> ys : ListN (ArrayN a nc1) (len xs) -> zs : ListN (ArrayN a nc2) (len xs) -> ListN (ArrayN a { 1 + nc1 + nc2 }) (len xs) @-}
{-@ reflect makeT3 @-}
makeT3 :: (Eq a) => Int -> Int -> [a] -> [Array a] -> [Array a] -> [Array a]
makeT3 nc1 nc2 ([]) ([]) ([]) = []
makeT3 nc1 nc2 (x:xs) (y:ys) (z:zs) = makeT x y z : (makeT3 nc1 nc2 xs ys zs)

{-@ makeArray :: (Eq a) => xs: [a] -> arr : ArrayN a { len xs } @-}
makeArray ::(Eq a) => [a] -> Array a
makeArray [] = Nil
makeArray xs = head arr
  where
    (IArray _ i arr arr2 k) = (build (rows 1 xs))
