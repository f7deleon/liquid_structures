{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--reflect" @-}
{-@ LIQUID "--ple" @-}


{- Based on https://www.cs.uleth.ca/~gaur/post/avl/ representation -}
module AVLTrees where
import Prelude hiding (max,min, abs, max, min, exponent, lookup, take, drop, repeat, head, tail, concat, even)
import GHC.TypeNats (Nat)

{-@ inline max @-}
{-@ max :: (Ord a) => a -> a -> a @-}
max :: (Ord a) => a -> a -> a
max x y =
  if x > y
    then x
    else y
    
{-@ inline min @-}
{-@ min :: (Ord a) => a -> a -> a @-}
min :: (Ord a) => a -> a -> a
min x y =
  if x < y
    then x
    else y

{-@ inline abs @-}
{-@ abs :: Int -> v : { Int | v >= 0 }@-}
abs :: Int -> Int
abs x = if x < 0 then -x else x


{-@ height :: (Ord a) => AVL a -> Nat @-}
height :: (Ord a) => AVL a -> Int
height Nil = 0
height (Node _ l r _) = 1 + maxHeight l r
{-@ measure height @-}

{-@ mheight :: (Ord a) => AVL a -> Nat @-}
mheight :: (Ord a) => AVL a -> Int
mheight Nil = 0
mheight (Node _ l r _) = 1 + minHeight l r
{-@ measure mheight @-}

{-@ inline maxHeight @-}
{-@ maxHeight :: (Ord a) => AVL a -> AVL a -> Nat @-}
maxHeight ::(Ord a) => AVL a -> AVL a -> Int
maxHeight l r = max (height l) (height r)

{-@ inline minHeight @-}
{-@ minHeight :: (Ord a) => AVL a -> AVL a -> Nat @-}
minHeight ::(Ord a) => AVL a -> AVL a -> Int
minHeight l r = min (height l) (height r)



{-@ inline weightLR @-}
{-@ weightLR :: (Ord a) => l: AVL a -> r: AVL a -> w : Int @-}
weightLR :: (Ord a) => AVL a -> AVL a-> Int
weightLR l r = getHeight l - getHeight r

{-@ measure weight @-}
{-@ weight :: AVL a -> w : { Int | w >= -1 && w <= 1}@-}
weight :: (Ord a) => AVL a -> Int
weight (Nil) = 0
weight (Node _ l r _) = getHeight l - getHeight r

{-@ inline balanced @-}
{-@ balanced :: (Ord a) => l: AVL a -> r:AVL a -> v: { Bool | v <=> (height l == height r || height l  == height r + 1 || height l == height r -1) } @-}
balanced :: (Ord a) => AVL a -> AVL a -> Bool 
balanced t1 t2 = abs (weightLR t1 t2) <= 1

data AVL a where
  Node :: Ord a => a -> AVL a -> AVL a -> Int -> AVL a
  Nil :: Ord a => AVL a

{-@
data AVL a where
  Node :: Ord a => x: a -> 
    l: AVL { vv : a |  x > vv } -> 
    r: { AVL { vv: a | x < vv }| balanced l r } ->
    h: { Int | h == 1 + (max (height l) (height r)) } -> 
    f: AVL a
  Nil :: Ord a => AVL a
@-}


{-@ inline even @-}
even :: Int -> Bool
even x = if (mod x 2) == 0 then True else False

{-@ single :: (Ord a) => a -> { t : AVL a | height t == 1 } @-}
single :: (Ord a) => a -> AVL a
single a = Node a Nil Nil 1

{-@ notEmpty :: t: AVL a -> v: { Bool | v <=> not (isEmpty t) } @-}
notEmpty :: AVL a -> Bool
notEmpty Nil = False
notEmpty (Node v _ _ _) = True

{-@ measure notEmpty @-}

{-@ isEmpty :: t: AVL a -> v: { Bool | v <=> not (notEmpty t) } @-}
isEmpty :: AVL a -> Bool
isEmpty Nil = True
isEmpty (Node v _ _ _) = False
{-@ measure isEmpty @-}

{-@ test :: AVL Int @-}
test :: AVL Int
test = Node 6 l r 3
  where
    l = Node 4 (single 3) (Nil) 2
    r = Node 8 (single 7) (single 9) 2

{-@ fail test2 @-}
{-@ test2 :: AVL Int @-}
test2 :: AVL Int
test2 = Node 6 l r 3
  where
    l = Nil
    r = Node 8 (single 7) (single 9) 2

{-@ getHeight :: t : AVL a -> {h: Int | height t == h }@-}
getHeight :: AVL a -> Int
getHeight Nil = 0
getHeight (Node _ _ _ h) = h
{-@ measure getHeight @-}

{-@ makeT ::  v : a -> l : AVL { v2 : a | v2 < v} -> r: { AVL { v2 : a | v2 > v} | balanced l r } -> f : { AVL a | height f == (1 + maxHeight l r )} @-}
makeT :: (Ord a) => a -> AVL a -> AVL a -> AVL a
makeT  v l r  = Node v l r (1 + max (getHeight l) (getHeight r))

{-@ inline insertPC @-}
insertPC :: (Ord a) => AVL a -> AVL a -> Bool
insertPC f t = fh == th || fh == th + 1 
  where 
    th = height t
    fh = height f

{-@ insert :: (Ord a) -> t: AVL a -> a -> tf : { AVL a | insertPC tf t } @-}
insert :: (Ord a) => AVL a -> a -> AVL a
insert Nil v = Node v Nil Nil 1
insert t@(Node v l r _) v2 
  | v > v2 = balance v (insert l v2) r
  | v < v2 = balance v l (insert r v2)
  | otherwise = t

{-@ inline balancePC @-}
{-@ 
balancePC :: (Ord a) => l : AVL a ->
 r:{ AVL a| abs (weightLR l r)  <= 2 } -> 
 f : AVL a -> Bool
@-}
balancePC :: (Ord a) => AVL a -> AVL a -> AVL a -> Bool
balancePC f l r 
  | td > 0 && wl == 0 = height f == hl + 1 
  | td > 0 = height f == hr + 2
  | td < 0 && wr == 0 = height f == hr + 1
  | td < 0 = height f == hl + 2 
  | otherwise = height f == 1 + maxHeight l r
  where
    td = hl - hr
    hl = height l
    hr = height r
    wl = weight l
    wr = weight r

-- {-@ inline balancePC @-}
-- balancePC :: (Ord a) => AVL a -> AVL a -> AVL a -> Bool
-- balancePC f l r = hf == 2 + minh || hf == 1 + maxh
--   where
--     maxh = maxHeight l r
--     minh = minHeight l r 
--     hf = height f

{-@
balance :: (Ord a) => x: a 
          -> l : AVL { v: a | v < x }
          -> r:{ AVL { v: a | v > x } | weightLR l r  <= 2 && weightLR l r  >= -2}
          -> f : { AVL a | balancePC f l r }
@-}
balance :: (Ord a) => a -> AVL a -> AVL a -> AVL a
balance v l r 
  | td == 2 && wl == 0 = balL0 v l r
  | td == 2 && wl == 1 = balLL v l r
  | td == 2 && wl == -1 = balLR v l r
  | td == -2 && wr == 0 = balR0 v l r
  | td == -2 && wr == 1 = balRL v l r
  | td == -2 && wr == -1 = balRR v l r
  | otherwise = Node v l r (1 + max (getHeight l) (getHeight r))
  where
    td = weightLR l r 
    wl = weight l
    wr = weight r 

{-@ balL0 :: x:a
          -> l:{ AVL {v:a | v < x} | weight l == 0 }
          -> r:{ AVL {v:a | v > x} | weightLR l r == 2 }
          -> { t: AVL a | height t == height l + 1 }
  @-}
balL0 v (Node lv ll lr _) r = makeT lv ll (makeT v lr r)

{-@ balLR :: x:a
          -> l:{ AVL { v:a | v < x } | weight l == -1 }
          -> r:{ AVL { v:a | v > x } | weightLR l r == 2 }
          -> { t : AVL a | height t == height l }
  @-}
balLR v (Node lv ll (Node lrv lrl lrr _) _) r
  = makeT lrv (makeT lv ll lrl) (makeT v lrr r)

{-@ balLL :: x:a
          -> l:{ AVL { v:a | v < x } | weight l == 1 }
          -> r:{ AVL { v:a | v > x } | weightLR l r == 2 }
          -> { t : AVL a | height t == height l }
  @-}
balLL :: (Ord a) => a -> AVL a -> AVL a -> AVL a
balLL v (Node lv ll lr _) r = makeT lv ll (makeT v lr r)

{-@ balR0 :: x:a
          -> l: AVL {v:a | v < x}
          -> r:{ AVL {v:a | v > x} | weightLR l r == -2 && weight r == 0 }
          -> { t: AVL a | height t == height r + 1 }
  @-}
balR0 :: (Ord a) => a -> AVL a -> AVL a -> AVL a
balR0 v l (Node rv rl rr _) = makeT rv (makeT v l rl) rr

  {-@ balRR :: x:a
          -> l: AVL { v: a | v < x }
          -> r:{AVL { v: a | v > x } | weightLR l r == -2 && weight r == -1 }
          -> {t: AVL a | height t == height r }
  @-}
balRR :: (Ord a) => a -> AVL a -> AVL a -> AVL a
balRR v l (Node rv rl rr _) = makeT rv (makeT v l rl) rr

{-@ balRL :: x:a
          -> l: AVL { v: a | v < x }
          -> r:{AVL { v: a | v > x } | weightLR l r == -2 && weight r == 1 }
          -> { t: AVL a | height t == height r }
  @-}
balRL :: (Ord a) => a -> AVL a -> AVL a -> AVL a
balRL v l (Node rv (Node rlv rll rlr _) rr _) = makeT rlv (makeT v l rll) (makeT rv rlr rr)

{-@ inline deletePC @-}
deletePC :: (Ord a) => AVL a -> AVL a -> Bool 
deletePC f t =  height f == height t || height f == height t - 1 

{-@ delete :: (Ord a) => t : AVL a -> v : a -> f: { AVL a | deletePC f t }@-}
delete :: (Ord a) => AVL a -> a -> AVL a
delete Nil _ = Nil
delete t@(Node v l r _) v2 
  | v > v2 = balance v (delete l v2) r 
  | v < v2 = balance v l (delete r v2) 
  | otherwise = merge v l r

{-@ inline mergePC @-}
{-@  mergePC :: (Ord a) => l: AVL a -> r : { AVL a | balanced l r } -> f: AVL a -> Bool @-}
mergePC :: (Ord a) => AVL a -> AVL a -> AVL a -> Bool
mergePC l r f   
  | td == 1 = hl == fh || hl + 1 == fh
  | otherwise = rh == fh || rh + 1 == fh
  where
    td = weightLR l r 
    rh = height r
    hl = height l
    fh = height f

{-@ merge :: (Ord a) =>  v : a -> l: AVL {vv: a | v > vv } ->
                         r : { AVL {vv: a | vv > v} | balanced l r } ->
                         f: { AVL a | mergePC l r f }
                        @-}
merge :: (Ord a) => a -> AVL a -> AVL a -> AVL a 
merge _ (Nil) t = t
merge _ l r = balance mv mt r
  where 
    (mv, mt) = maxValue l

{-@ maxValue :: (Ord a) =>  t : { AVL a | notEmpty t } -> p:{ (v::a, AVL { vv : a | vv < v }) | deletePC (snd p) t }@-}
maxValue ::(Ord a) => AVL a -> (a, AVL a) 
maxValue (Node v l Nil _) = (v, l)
maxValue (Node v l r h) = (v3, balance v l r2)
  where
    (v3, r2) = maxValue r

makeTreeFromList :: (Ord a) => [a] -> AVL a 
makeTreeFromList [] = Nil
makeTreeFromList (x:xs) = insert (makeTreeFromList xs) x  
