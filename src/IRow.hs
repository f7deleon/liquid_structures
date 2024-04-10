
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}

module IRow where
import ImprovedList
import Prelude hiding (even, abs, max, min, exponent, lookup, take, drop, repeat, head, tail, concat)

data IRow a where
  Last :: (Eq a) => Int -> [a] -> IRow a
  IRow :: (Eq a) => Int -> [a] -> IRow a -> IRow a

{-@
data IRow a where
  Last :: (Eq a) => { n: Nat | n > 0} -> { l: [a] | len l > 0 && len l <= n } -> IRow a
  IRow :: (Eq a) => { n: Nat | n > 0} -> { l : [a] | len l == n } -> {r : IRow a | size r == 2 * n } -> IRow a
@-}

countRowNodes :: (Eq a) => IRow a -> Int
countRowNodes (Last _ xs) = length2 xs
countRowNodes (IRow _ xs next) = length2 xs + countRowNodes next
{-@ measure countRowNodes @-}

size :: (Eq a) => IRow a -> Int
size (Last k _) =k
size (IRow i _ _) = i
{-@ measure size @-}

getL :: (Eq a) => IRow a ->[a]
getL (Last _ l) = l
getL (IRow _ l _) = l

{-@ rows :: (Eq a) => { n : Nat | n > 0 }-> { xs:[a] | len xs > 0 }-> { ir : IRow a | size ir == n && countRowNodes ir == len xs }@-}
{-@ reflect rows @-}
rows ::(Eq a) => Int -> [a] -> IRow a
rows k xs
  | notEmptyL d = IRow k t (rows (2 * k) d)
  | otherwise = Last k xs
  where
  (t,d) = split k xs

{-@ measure iRowToList @-}
{-@ iRowToList :: ir : IRow a -> xs: { [a] | countRowNodes ir == len xs }@-}
iRowToList :: (Eq a) => IRow a -> [a]
iRowToList (Last _ t) = t
iRowToList (IRow _ t next) = concat t ir
  where
    ir = iRowToList next
