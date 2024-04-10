{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflect" @-}
{-@ LIQUID "--ple" @-}

{-# OPTIONS_GHC -XPackageImports #-}
{-# LANGUAGE GADTs #-}

module LiquidVector where
import Prelude hiding (length)
import Language.Haskell.Liquid.ProofCombinators

data Vector a where
  Cons :: a -> Int -> Vector a -> Vector a
  Empty :: Vector a

{-@ reflect length @-}
length :: Vector a -> Int
length (Cons _ _ next) = 1 + length next  
length (Empty) = 0


isEmpty :: Vector a -> Bool
isEmpty Empty = True
isEmpty _ = False
{-@ reflect isEmpty @-}

notEmpty :: Vector a -> Bool
notEmpty Empty = False
notEmpty _ = True
{-@ reflect notEmpty @-}

{-@ isEmptyThenEmpty :: t : { Vector a | isEmpty t } -> { t == Empty }@-}
isEmptyThenEmpty :: Vector a -> Proof
isEmptyThenEmpty Empty = trivial *** QED
isEmptyThenEmpty t = isEmpty t == False *** QED

{-@ reflect insert @-}
insert :: (Ord a) => Vector a -> a -> Vector a 
insert (Empty) v =  Cons v 1 Empty
insert t@(Cons v l next) v2 = Cons v2 (l + 1) t

{-@ value :: t :{ Vector Char | notEmpty t} -> Char @-}
value :: Vector Char -> Char
value (Cons v _ _) = v

{-@ insertLength :: (Ord a) => t :  Vector a -> v: a -> { length (insert t v) == 1 + length t }@-}
insertLength ::(Ord a) => Vector a -> a -> Proof
insertLength Empty v = length (insert Empty v) == 1 + length Empty
  === length (Cons v 1 Empty) == 1
  === 1 + length Empty == 1
  === 1 == 1 *** QED
insertLength vec@(Cons v l next) v2 = length (insert vec v2) == 1 + length vec 
                    ===  length (Cons v2 (l + 1) vec) == 1 + length vec
                    === 1 + length vec == 1 + length vec
                    *** QED

{-@ insertLength2 :: (Ord a) => t :  Vector a -> v: a -> { length (insert t v) == 1 + length t }@-}
insertLength2 ::(Ord a) => Vector a -> a -> Proof
insertLength2 Empty v = trivial *** QED
insertLength2 vec@(Cons v l next) v2 = insertLength2 next v