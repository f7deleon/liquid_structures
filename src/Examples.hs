{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}
{-@ LIQUID "--prune-unsorted" @-}


module Examples where
import Prelude hiding (even, break, length)

{-@ inline even @-}
even :: Int -> Bool
even x = if (mod x 2) == 0 then True else False

{-@ measure allEven @-}
{-@ allEven :: [Int] -> Bool @-}
allEven :: [Int] -> Bool
allEven [] = True
allEven (x:xs) = even x && allEven xs

{-@ type EvenList = xs: { [Int] | allEven xs } @-}

{-@ t1 :: EvenList @-}
t1 :: [Int]
t1 = [2,4,6,8]

{-@ t2 :: EvenList@-}
{-@ fail t2 @-}
t2 :: [Int]
t2 = [3]

{-@ t3 :: EvenList@-}
{-@ fail t3 @-}
t3 :: [Int]
t3 = [2,4,3,6,8]

{-@ measure length @-}
length :: [a] -> Int
length (x:xs) = 1 + length xs
length [] = 0
