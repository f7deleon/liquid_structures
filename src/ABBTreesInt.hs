
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflect" @-}
{-# LANGUAGE GADTs #-}

module ABBTreesInt where
import Language.Haskell.Liquid.ProofCombinators
import Language.Haskell.Liquid.Prelude hiding (min, max)
import Basics

data Tree a where
  Node :: (Ord a) => a -> Tree a -> Tree a -> Tree a
  Nil :: Tree a

{-@
data Tree a where
  Node :: (Ord a) => v : a -> Tree {vv: a | v >= vv} -> Tree {vv: a | v < vv} -> Tree a
  Nil :: Tree a
@-}

{-@ test1 :: Tree Int @-}
test1 :: Tree Int
test1 = Node 6 (Node 4 (Node 3 (Nil) (Nil)) (Node 6 (Nil) (Nil))) (Node 7 (Node 7 (Nil) (Nil)) (Node 16 (Nil) (Nil)))

{-@ test2 :: Tree Int @-}
{-@ fail test2 @-}
test2 :: Tree Int
test2 = Node 6 (Node 4 (Node 3 (Nil) (Nil)) (Node 7 (Nil) (Nil))) (Node 7 (Node 7 (Nil) (Nil)) (Node 16 (Nil) (Nil)))

insert :: (Ord a) => Tree a -> a -> Tree a
insert (Nil) v = Node v Nil Nil 
insert (Node v2 l r) v
    | v <= v2 = Node v2 (insert l v) r
    | otherwise = Node v2 l (insert r v)

delete :: (Ord a) => Tree a -> a -> Tree a
delete (Nil) v = Node v Nil Nil 
delete (Node v2 l r) v
    | v < v2 = Node v2 (insert l v) r
    | v > v2 = Node v2 l (insert r v)
    | otherwise = merge v r l

{-@ merge :: (Ord a) =>  v : a -> Tree {vv: a | v < vv} -> Tree {vv: a | vv <= v } -> Tree a @-}
merge :: (Ord a) => a -> Tree a -> Tree a -> Tree a 
merge v (Nil) t = t
merge v (Node v2 l r) t = (Node v2 (merge v l t) r)

search :: (Ord a) =>  Tree a -> a -> Maybe a 
search (Nil) v = Nothing
search (Node v2 l r) v 
    | v < v2 = (search l v) 
    | v > v2 = (search r v)
    | otherwise = Just v2
