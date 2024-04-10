  
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}

module ImprovedList where
import Prelude hiding (even, abs, max, min, exponent, lookup, take, drop, repeat, head, tail, concat)
import Basics


{-@ lookupL :: i : Nat ->  xs : {[a] | length2 xs > i} -> a @-}
lookupL :: Int -> [a] -> a
lookupL 0 (x:xs) = x
lookupL n (x:xs) = lookupL (n - 1) xs
{-@ reflect lookupL @-}

{-@ take :: n : Nat -> l : [a] -> {lf: [a] | len lf == 0 <=> (n == 0 || len l == 0) && (len l < n => len lf == len l) && (len l >= n => len lf == n) }@-}
take :: Int -> [a] -> [a]
take _ [] = []
take 0 _ = []
take n (x:xs) = x : (take (n-1) xs)

{-@ drop :: n : Nat -> l : [a] -> { lf : [a] | len l >= n => len lf == len l - n }@-}
drop :: Int -> [a] -> [a]
drop _ [] = []
drop 0 xs = xs
drop n (x:xs) = (drop (n-1) xs)

{-@ concat :: xs: [a] -> ys: [a] -> zs: { [a] | len zs == len xs + len ys }@-}
{-@ reflect concat @-}
concat :: [a] -> [a] -> [a]
concat [] ys = ys
concat (x:xs) ys = x : concat xs ys

{-@ measure notEmptyL @-}
{-@ notEmptyL :: xs: [a] -> v :{ Bool | (v <=> len xs > 0) && (v <=> not (isEmptyL xs)) }@-}
notEmptyL :: [a] -> Bool
notEmptyL [] = False
notEmptyL xs = True

{-@ measure isEmptyL @-}
{-@ isEmptyL :: xs: [a] -> v :{ Bool | (v <=> len xs == 0) && (v <=> not (notEmptyL xs)) }@-}
isEmptyL :: [a] -> Bool
isEmptyL [] = True
isEmptyL (x:xs) = False

{-@ head :: xs: { [a] | notEmptyL xs } -> a @-}
head :: [a] -> a
head (x:xs) = x
{-@ measure head @-}

app :: (a, [a]) -> [a]
app (x,xs) = x:xs
{-@ measure app @-}

{-@ tail :: xs : { [a] | notEmptyL xs } -> {ys : [a] | len ys == len xs -1 } @-}
tail :: [a] -> [a]
tail (_:xs) = xs
{-@ measure tail @-}

{-@ reflect split @-}
{-@ type SPair a XS N = { p: ([a],[a]) | len (fst p) == min N (len XS) && len (snd p) == max 0 (len XS - N) } @-}
{-@ split :: n: Nat -> xs: [a] -> p : { SPair a xs n | concat (fst p) (snd p) == xs && (len (fst p) == n => len (snd p) == n - len xs) || (isEmptyL (snd p) => len (fst p) == len xs) }@-}
split :: Int -> [a] -> ([a],[a])
split _ [] = ([],[])
split 0 xs = ([],xs)
split k (x:xs) = (x:d, l)
  where
    (d, l) = split (k-1) xs


{-@ length2 :: xs:[a] -> n : {Nat | n == len xs }@-}
length2 :: [a] -> Int
length2 [] = 0
length2 (x:xs) = 1 + length2 xs
{-@ measure length2 @-}

{-@ compleate :: n:Nat -> a -> [a] -> {xs : [a] | len xs == n }@-}
{-@ reflect compleate @-}
compleate :: Int -> a -> [a] -> [a]
compleate 0 _ _ = []
compleate n v [] = v : (compleate (n-1) v [])
compleate n v (x:xs) = x : (compleate (n - 1) v xs)

type List a = [a]
{-@ type ListN a N = { l : [a] | len l == N } @-}
