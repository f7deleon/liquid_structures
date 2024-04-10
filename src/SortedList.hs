{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

{-# OPTIONS_GHC -XPackageImports #-}
{-# LANGUAGE GADTs #-}

module SortedList where
import Prelude hiding (length, even)
import Basics



data Vector a where
  Cons :: a -> Int -> Vector a -> Vector a
  Empty :: Vector a

{-@
data Vector a where
    Cons :: a -> l : Int -> 
        next : { Vector a | l == length next + 1 }-> Vector a
    Empty :: Vector a
@-}

{-@ measure length @-}
length :: Vector a -> Int
length (Cons _ _ next) = 1 + length next  
length (Empty) = 0


test1 :: Vector Int
test1 = Cons 1 4 (Cons 2 3 (Cons 3 2 (Cons 4 1 Empty)))

{-@ fail test2 @-}
test2 :: Vector Int
test2 = Cons 1 5 (Cons 2 3 (Cons 3 2 (Cons 4 1 Empty)))

{-@ measure allEven @-}
{-@ allEven :: Vector Int -> Bool @-}
allEven :: Vector Int -> Bool
allEven Empty = True
allEven (Cons v _ next) = even v && allEven next

