
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflect" @-}
{-@ LIQUID "--ple-local" @-}

{-# OPTIONS_GHC -XPackageImports #-}
{-# LANGUAGE GADTs #-}

module ABBTreesExt where
import Prelude hiding (min, max)
import Basics

data Tree a where
  Node :: (Ord a) => a -> Tree a -> Tree a -> Tree a
  Nil :: (Ord a) => Tree a
  
notEmpty :: (Ord a) => Tree a -> Bool
notEmpty Nil = False
notEmpty (Node _ _ _) = True
{-@ measure notEmpty @-}

{-@ isEmpty :: (Ord a) => t : Tree a -> v: {Bool| v <=> not (notEmpty t)} @-}
isEmpty :: (Ord a) => Tree a -> Bool
isEmpty Nil = True
isEmpty (Node _ _ _) = False
{-@ measure isEmpty @-}

{-@ measure greatest @-}
{-@ greatest :: (Ord a) => t: { Tree a | notEmpty t } -> v : a  @-}
greatest :: (Ord a) => Tree a -> a
greatest (Node v l r)
  | notEmpty l && notEmpty r = max (max (greatest l) (greatest r)) v
  | notEmpty l = max (greatest l) v
  | notEmpty r = max (greatest r) v
  | otherwise = v

{-@ measure lowest @-}
{-@ lowest :: (Ord a) => t: { Tree a | notEmpty t } -> v :  a @-}
lowest :: (Ord a) => Tree a -> a
lowest (Node v l r) 
  | notEmpty l && notEmpty r = min (min (lowest l) (lowest r)) v
  | notEmpty l = min (lowest l) v
  | notEmpty r = min (lowest r) v
  | otherwise = v

{-@ isABB :: (Ord a) => t : Tree a -> Bool @-}
isABB :: Tree a -> Bool
isABB (Nil) = True
isABB  t@(Node v l r)
  | notEmpty l && notEmpty r && leafsABB = v > (greatest l) && v < (lowest r)
  | notEmpty l && leafsABB = v > (greatest l)
  | notEmpty r && leafsABB = v < (lowest r)
  | otherwise = leafsABB
  where
    leafsABB = isABB l && isABB r
{-@ measure isABB @-}


{-@ type ABB a = t: { Tree a | isABB t } @-}
{-@ type ABBNE a = t: { Tree a | isABB t && notEmpty t } @-}

{-@ test1 :: ABB Int @-}
test1 :: Tree Int
test1 = Node 6 (Node 4 (Node 3 (Nil) (Nil)) (Node 5 (Nil) (Nil))) (Node 8 (Node 7 (Nil) (Nil)) (Node 16 (Nil) (Nil)))

{-@ test2 :: ABB Int @-}
{-@ fail test2 @-}
test2 :: Tree Int
test2 = Node 6 (Node 4 (Node 3 (Nil) (Nil)) (Node 7 (Nil) (Nil))) (Node 7 (Node 7 (Nil) (Nil)) (Node 16 (Nil) (Nil)))

{-@ insertPostCondition:: (Ord a) => tf : { ABB a | notEmpty tf }-> ABB a -> a -> Bool @-}
insertPostCondition :: (Ord a) => Tree a -> Tree a -> a -> Bool
insertPostCondition tf t v 
    | notEmpty t = (greatest tf == greatest t || greatest tf == v) && (lowest tf == lowest t || lowest tf == v)
    | otherwise = (greatest tf == v) && (lowest tf == v)
{-@ inline insertPostCondition @-}

{-@ insert :: t : ABB a -> v : a -> tf: { ABBNE a | insertPostCondition tf t v } @-}
insert :: (Ord a) => Tree a -> a -> Tree a
insert (Nil) v = Node v Nil Nil 
insert t@(Node v l r) k
    | v > k = Node v (insert l k) r
    | v < k = Node v l (insert r k) 
    | otherwise = t

{-@ deletePostCondition:: (Ord a) => tf :  ABB a -> t : ABB a -> Bool @-}
deletePostCondition :: (Ord a) => Tree a -> Tree a -> Bool
deletePostCondition tf t 
    | notEmpty tf && notEmpty t = (greatest tf == greatest t || greatest tf < greatest t) && (lowest tf == lowest t || lowest tf > lowest t)
    | otherwise = isEmpty tf
{-@ inline deletePostCondition @-}

{-@ delete :: t : ABB a -> v: a -> tf: { ABB a | deletePostCondition tf t } @-}
delete :: (Ord a) => Tree a -> a -> Tree a
delete (Nil) _ = Nil
delete t@(Node v l r) k
    | v > k = Node v (delete l k) r
    | v < k = Node v l (delete r k) 
    | otherwise = merge r l

{-@ mergePostCondition :: (Ord a) => r :  ABB a -> l : ABB a -> f : ABB a -> Bool @-}
mergePostCondition :: (Ord a) => Tree a -> Tree a -> Tree a -> Bool
mergePostCondition r l f
    | notEmpty l && notEmpty r && notEmpty f = lowest f >= (lowest l) && greatest f <= (greatest r)
    | notEmpty l && isEmpty r && notEmpty f = lowest f == lowest l && greatest f == greatest l
    | isEmpty l && notEmpty r && notEmpty f = lowest f == lowest r && greatest f == greatest r
    | otherwise = isEmpty f
{-@ inline mergePostCondition @-}

{-@ merge :: (Ord a) => r : ABB a  -> l : { ABB a | (notEmpty l && notEmpty r) => greatest l < lowest r } -> f : { ABB a | mergePostCondition r l f }    @-}
merge :: (Ord a) => Tree a -> Tree a -> Tree a 
merge r@(Node v2 l2 r2) l@(Node _ _ _) = Node v2 (merge l2 l) r2
merge (Nil) l@(Node _ _ _) = l
merge r@(Node _ _ _) (Nil) = r
merge (Nil) (Nil) = Nil

search :: (Ord a) =>  Tree a -> a -> Maybe a 
search (Nil) v = Nothing
search (Node v2 l r) v 
    | v < v2 = (search l v) 
    | v > v2 = (search r v)
    | otherwise = Just v2

