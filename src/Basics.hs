{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-# LANGUAGE GADTs #-}

module Basics where
import Prelude hiding (min, max)

{-@ inline max @-}
{-@ max :: (Ord a) => a -> a -> a @-}
max :: (Ord a) => a -> a -> a
max x y = if x >= y then x else y

{-@ inline min @-}
{-@ min :: (Ord a) => a -> a -> a @-}
min :: (Ord a) => a -> a -> a
min x y = if x < y then x else y

{-@ even :: n : Int -> Bool @-}
even :: Int -> Bool
even i = i `mod` 2 == 0
{-@ reflect even @-} {- Make all work -}
