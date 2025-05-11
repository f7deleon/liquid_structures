{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module LogProofs where
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (even, abs, max, min, exponent, pow, take, drop, repeat, head, tail, lookup)
import BraunTree
import BasicOperations
import ImprovedList
import Basics

{-@ node_count_max_inequallity_proof :: t : BTree a -> { nodeCount t + nodeCount t + 1 <= 2 * pow2 (h t) - 1 }  @-}
node_count_max_inequallity_proof :: Tree a -> Proof
node_count_max_inequallity_proof (Nil) = ()
node_count_max_inequallity_proof t =nodeCount t + nodeCount t + 1 <= 2 * pow2 (h t) - 1
                                === nodeCount t + nodeCount t + 1 <= 2 * pow2 (h t) - 1
                                === 2 * nodeCount t <= 2 * pow2 (h t) - 2
                                === nodeCount t <= pow2 (h t) - 1 ? node_count_max t
                                *** QED

{-@ node_count_max :: t :  BTree a -> { nodeCount t <= pow2 (h t) - 1} @-}
node_count_max :: Tree a -> Proof
node_count_max (Nil) = ()
node_count_max t@(Node _ Nil Nil) = ()
node_count_max t@(Node _ l r) 
      | h l >= h r && nodeCount l >= nodeCount r = nodeCount t  <= pow2 (h t) - 1
                  === 1 + nodeCount l + nodeCount r <= pow2 (1 + h l) - 1
                  === 1 + nodeCount l + nodeCount r <= 2 * pow2 (h l) - 1 
                  ? (1 + nodeCount l + nodeCount r <=  1 + nodeCount l + nodeCount l) 
                  ? node_count_max_inequallity_proof l
                  *** QED
      | h l < h r && nodeCount l <= nodeCount r = nodeCount t  <= pow2 (h t) - 1
                  === 1 + nodeCount l + nodeCount r <= pow2 (1 + h r) - 1
                  === 1 + nodeCount l + nodeCount r <= 2 * pow2 (h r) - 1 
                  ? (1 + nodeCount l + nodeCount r <= 1 + nodeCount r + nodeCount r) 
                  ? node_count_max_inequallity_proof r
                  *** QED
      | h l >= h r && nodeCount l < nodeCount r = nodeCount t <= pow2 (h t) -1
                  === 1 + nodeCount l + nodeCount r <= pow2 (1 + h l) -1
                  === 1 + nodeCount l + nodeCount r <= 2 * pow2 (h l) - 1
                  ? (1 + nodeCount l + nodeCount r <= nodeCount r + nodeCount r + 1)
                  ? (
                    nodeCount r + nodeCount r + 1 <= 2 * pow2 (h l) - 1
                    ===  2 * (nodeCount r) <= 2 * pow2 (h l) - 2
                    === nodeCount r <= pow2 (h l) - 1 ? (pow2 (h r) -1 <= pow2 (h l) -1)
                    ? (nodeCount r <= pow2 (h r) - 1 ? node_count_max r *** QED)
                    )
                  *** QED
      | h l < h r && nodeCount l > nodeCount r = nodeCount t <= pow2 (h t) -1
                  === 1 + nodeCount l + nodeCount r <= pow2 (1 + h r) -1
                  === 1 + nodeCount l + nodeCount r <= 2 * pow2 (h r) -1
                  ? (1 + nodeCount l + nodeCount r <= nodeCount l + nodeCount l + 1)
                  ? (
                    nodeCount l + nodeCount l + 1 <= 2 * pow2 (h r) -1
                    ===  2 * (nodeCount l) <= 2 * pow2 (h r) - 2 
                    === nodeCount l <= pow2 (h r) -1 ? (pow2 (h l) -1 <= pow2 (h r) -1)
                    ? (nodeCount l <= pow2 (h l) -1 ? node_count_max l *** QED)
                    )
                  *** QED
                
{-@ corolary_node_max :: t: BTree a -> { nodeCount t < pow2 (h t) } @-}
corolary_node_max :: Tree a -> Proof
corolary_node_max (Nil) = ()
corolary_node_max t@(Node _ l r) = nodeCount t < pow2 (h t)
                                    ? (pow2 (h t) -1 < pow2 (h t))
                                    ? (nodeCount t <= pow2 (h t) -1 ? node_count_max t *** QED)
                                    *** QED

{-@ node_count_min :: t: BTree a -> { nodeCount t >= pow2 (mh t) - 1 }  @-}                  
node_count_min :: Tree a -> Proof 
node_count_min (Nil) = ()
node_count_min t@(Node _ l r) 
       | mh l < mh r && nodeCount l >= nodeCount r = nodeCount t  >= pow2 (mh t) - 1
                  === 1 + nodeCount l + nodeCount r >= pow2 (1 + mh l) - 1
                  === 1 + nodeCount l + nodeCount r >= 2 * pow2 (mh l) - 1 
                  ? (1 + nodeCount l + nodeCount r >=  1 + nodeCount r + nodeCount r) 
                  ? (
                      1 + nodeCount r + nodeCount r >= 2 * pow2 (mh l) - 1
                      === 2 * nodeCount r >= 2 * pow2 (mh l) - 2
                      === nodeCount r >= pow2 (mh l) - 1 ? 
                      (pow2 (mh r) - 1 >= pow2 (mh l) - 1) 
                      ? (nodeCount r >= pow2(mh r) - 1 ? node_count_min r *** QED)
                      )
                  *** QED
      | mh l >= mh r && nodeCount l <= nodeCount r = nodeCount t  >= pow2 (mh t) - 1
                  === 1 + nodeCount l + nodeCount r >= pow2 (1 + mh r) - 1
                  === 1 + nodeCount l + nodeCount r >= 2 * pow2 (mh r) - 1 
                  ? (1 + nodeCount l + nodeCount r >= 1 + nodeCount l + nodeCount l) 
                  ? (
                      nodeCount l + nodeCount l + 1 >= 2 * pow2 (mh r) - 1
                      === 2 * nodeCount l >= 2 * pow2 (mh r) -2
                      === nodeCount l >= pow2 (mh r) - 1 ?
                      (pow2 (mh l) -1 >= pow2 (mh r) - 1) ? (nodeCount l >= pow2(mh l) - 1 ? node_count_min l *** QED)
                      )
                  *** QED
      | mh l < mh r && nodeCount l < nodeCount r = nodeCount t >= pow2 (mh t) -1
                  === 1 + nodeCount l + nodeCount r >= pow2 (1 + mh l) -1
                  === 1 + nodeCount l + nodeCount r >= 2 * pow2 (mh l) - 1
                  ? (1 + nodeCount l + nodeCount r >= nodeCount l + nodeCount l + 1)
                  ? (
                    nodeCount l + nodeCount l + 1 >= 2 * pow2 (mh l) - 1
                    ===  2 * (nodeCount l) >= 2 * pow2 (mh l) - 2
                    === nodeCount l >= pow2 (mh l) - 1
                    ? node_count_min l
                    *** QED
                  )
                  *** QED
      | mh l >= mh r && nodeCount l > nodeCount r = nodeCount t >= pow2 (mh t) -1
                  === 1 + nodeCount l + nodeCount r >= pow2 (1 + mh r) -1
                  === 1 + nodeCount l + nodeCount r >= 2 * pow2 (mh r) -1
                  ? (1 + nodeCount l + nodeCount r >= nodeCount r + nodeCount r + 1)
                  ? (
                    nodeCount r + nodeCount r + 1 >= 2 * pow2 (mh r) -1
                    ===  2 * (nodeCount r) >= 2 * pow2 (mh r) - 2 
                    === nodeCount r >= pow2 (mh r) -1
                    ? node_count_min r
                    *** QED
                    )
                  *** QED

{-@ log_identity :: n : Nat -> { n == log2L (pow2 n) }@-}
log_identity :: Int -> Proof
log_identity 0 = ()
log_identity 1 = ()
log_identity n = n == log2L (pow2 n) === n == log2L (2 * pow2 (n - 1))
                === n == 1 + log2L (pow2 (n - 1))
                === n - 1 == log2L (pow2 (n -1)) 
                ? log_identity (n - 1)
                *** QED

{-@ log_limits :: i : Nat -> n : { Nat | pow2 i <= n && n < pow2 (i + 1) } ->  { log2L n == i }  @-}
log_limits :: Int -> Int -> Proof 
log_limits 0 0 = log2L 0 == 0 === 0 == 0 *** QED
log_limits 0 1 = log2L 1 == 0 === 0 == 0 *** QED
log_limits i n = log2L n == i 
                === 1 + log2L (div n 2) == 1 + (i - 1)
                === log2L (div n 2) == (i - 1)
                ? log_limits (i - 1) (div n 2)
                *** QED

{-@ diff_nc :: t : { BTree a | mh t + 1 == h t} -> { nodeCount t + 1 < pow2 (h t) } @-}
diff_nc :: Tree a -> Proof
diff_nc t@(Node _ l r) 
  | mh l < mh r && nodeCount l >= nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === 2 + nodeCount l + nodeCount r < pow2 (mh t + 1)
                                                ? (2 + nodeCount l + nodeCount r <= 2 + nodeCount l + nodeCount l)
                                                ? (2 + 2 * nodeCount l < pow2 (mh l + 2)
                                                === nodeCount l + 1< pow2 (mh l + 1)
                                                ? mh_node_count_limits2 l *** QED)
                                                *** QED
  | mh l >= mh r && nodeCount l <= nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === 2 + nodeCount l + nodeCount r < pow2 (mh t + 1) 
                                                ? (2 + nodeCount l + nodeCount r <= 2 + nodeCount r + nodeCount r)
                                                ? (2 + 2 * nodeCount r < pow2 (mh r + 2)
                                                === nodeCount r + 1 < pow2 (mh r + 1)
                                                ? mh_node_count_limits2 r *** QED)
                                                *** QED
  | mh l < mh r && nodeCount l < nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === nodeCount t + 1 < pow2 (mh t + 1)
                                                ? mh_node_count_limits2 t
                                                *** QED
  | mh l >= mh r && nodeCount l > nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === nodeCount t + 1 < pow2 (mh t + 1)
                                                ? mh_node_count_limits2 t
                                                *** QED

{-@ mh_node_count_limits2 :: t : BTree a -> { nodeCount t + 1 < pow2 (mh t + 1)} @-}
mh_node_count_limits2 :: Tree a -> Proof
mh_node_count_limits2 (Nil) = nodeCount (Nil) + 1 < pow2 (mh Nil + 1) === 1 < pow2 (0 + 1) === 1 < 2 *** QED
mh_node_count_limits2 t@(Node _ l r) 
      | mh t + 1 == h t = nodeCount t + 1 < pow2 (mh t + 1) 
                        === nodeCount t + 1 < pow2 (mh t + 1)
                        === nodeCount t + 1 < pow2 (mh t + 1)
                        === nodeCount t + 1 < pow2 (h t) ? diff_nc t
                        *** QED
      | mh t == h t = nodeCount t + 1 < pow2 (mh t + 1) 
                          === nodeCount t + 1 < pow2 (h t + 1)
                          === nodeCount t + 1 < 2 * pow2  (h t)
                          ? (pow2 (h t) < 2*pow2(h t))
                          ? (
                          nodeCount t < pow2 (h t) ? corolary_node_max t *** QED 
                          )*** QED


{-@ pow_log2_equallity :: t : { BTree a | mh t == h t } -> { pow2 (log2L (nodeCount t + 1)) == nodeCount t + 1 } @-}
pow_log2_equallity :: Tree a -> Proof
pow_log2_equallity (Nil) = ()
pow_log2_equallity t@(Node _ l r) = pow2 (log2L (nodeCount t + 1)) == nodeCount t + 1 ? mh_to_log2L t
                              === pow2 (mh t) == nodeCount t + 1
                              === pow2 (mh t) == nodeCount t + 1 
                              === pow2 (mh t) - 1 == nodeCount t ?
                                ((nodeCount t >= pow2 (mh t) - 1
                                  ? node_count_min t *** QED)
                                &&&
                                (nodeCount t <= pow2 (mh t) -1
                                ? node_count_max t *** QED))
                              *** QED

{-@ pow_log2_inequallity :: t : { BTree a | mh t + 1 == h t } -> { pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 }  @-}
pow_log2_inequallity :: Tree a -> Proof
pow_log2_inequallity t@(Node _ l r)  
    | mh l < mh r && nodeCount l < nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh l + 1) < nodeCount t + 1
                            === pow2 (mh l + 1) < 2 + nodeCount l + nodeCount r
                            ? (nodeCount l + nodeCount l < nodeCount l + nodeCount r)
                            ? (pow2 (mh l + 1) <= 2 * nodeCount l  + 2
                                === 2 * pow2 (mh l) <= 2 * nodeCount l + 2
                                === pow2 (mh l) <= nodeCount l + 1
                                === pow2 (mh l) - 1 <= nodeCount l
                                ? node_count_min l *** QED
                                )
                            *** QED
    | mh l < mh r && nodeCount l >= nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh l + 1) < nodeCount t + 1
                            === pow2 (mh l + 1) < 2 + nodeCount l + nodeCount r
                            ? (pow2 (mh l + 1) < pow2 (mh r + 1))
                            ? (pow2 (mh r +1) <= 2 + nodeCount l + nodeCount r 
                              ? (2 + 2 * nodeCount r <= 2 + nodeCount l + nodeCount r)
                              ? (
                                  pow2 (mh r + 1) <= 2 + 2 * nodeCount r 
                                  === pow2 (mh r) - 1 <= nodeCount r 
                                  ? node_count_min r *** QED 
                              ) *** QED
                           ) *** QED
    | mh l > mh r && nodeCount l > nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh r + 1) < nodeCount t + 1
                            === pow2 (mh r + 1) < 2 + nodeCount l + nodeCount r
                            ? (nodeCount r + nodeCount r < nodeCount l + nodeCount r)
                            ? (pow2 (mh r + 1) <= 2 * nodeCount r  + 2
                                === 2 * pow2 (mh r) <= 2 * nodeCount r + 2
                                === pow2 (mh r) <= nodeCount r + 1
                                === pow2 (mh r) - 1 <= nodeCount r
                                ? node_count_min r *** QED
                                )
                            *** QED
    | mh l > mh r && nodeCount l <= nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh r + 1) < nodeCount t + 1
                            === pow2 (mh r + 1) < 2 + nodeCount l + nodeCount r
                            ? (2 * nodeCount l + 2 <= 2 + nodeCount l + nodeCount r)
                            ? (pow2 (mh r + 1) < 2 * nodeCount l + 2
                                === pow2 (mh r) -1 < nodeCount l 
                                ? (pow2 (mh r) -1 < pow2 (mh l) -1)
                                ? (pow2 (mh l) -1 <= nodeCount l 
                                ? node_count_min l *** QED)
                                *** QED
                              )
                            *** QED
    | mh l == mh r && nodeCount l > nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh r + 1) < nodeCount t + 1
                            === pow2 (mh r + 1) < 2 + nodeCount r + nodeCount l
                            ? (nodeCount l > nodeCount r)
                            ? (pow2 (mh r + 1) <= 2 * nodeCount r + 2
                               === pow2 (mh r) -1 <= nodeCount r ? node_count_min r  *** QED  
                            )
                             *** QED
    | mh l == mh r && nodeCount l < nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh r + 1) < nodeCount t + 1
                            === pow2 (mh l + 1) < 2 + nodeCount r + nodeCount l
                            ? (nodeCount l < nodeCount r)
                            ? (pow2 (mh l + 1) <= 2 * nodeCount l + 2
                               === pow2 (mh l) -1 <= nodeCount l ? node_count_min l  *** QED  
                            )
                             *** QED
    | mh l == mh r && h l + 1 == h t && nodeCount l == nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh r + 1) < nodeCount t + 1
                            === pow2 (mh l + 1) < 2 + nodeCount l + nodeCount l
                            === 2 * pow2 (mh l) < 2 + 2 * nodeCount l
                            === pow2 (mh l) - 1 < nodeCount l ? pow_log2_inequallity l 
                            *** QED
    | mh l == mh r && h r + 1 == h t && nodeCount l == nodeCount r = pow2 (log2L (nodeCount t + 1)) < nodeCount t + 1 ? mh_to_log2L t
                            === pow2 (mh t) < nodeCount t + 1
                            === pow2 (mh r + 1) < nodeCount t + 1
                            === pow2 (mh r + 1) < 2 + nodeCount l + nodeCount l
                            === 2 * pow2 (mh r) < 2 + 2 * nodeCount r
                            === pow2 (mh r) - 1 < nodeCount r ? pow_log2_inequallity r 
                            *** QED


{-@ mh_to_log2L :: t : BTree a -> { log2L (nodeCount t + 1) == mh t } @-}
mh_to_log2L :: Tree a -> Proof
mh_to_log2L t = log2L (nodeCount t + 1) == mh t 
                            ? (
                                (
                                  nodeCount t + 1 >= pow2 (mh t)
                                  ? (pow2 (mh t) > pow2 (mh t) -1)
                                  ? (nodeCount t + 1 >= pow2 (mh t) -1 ? node_count_min t) 
                                  *** QED
                                )
                              &&&
                                (
                                  nodeCount t + 1 < pow2 (mh t + 1)
                                  ? mh_node_count_limits2 (t)
                                  *** QED
                                )
                              ***QED
                            )
                            ? log_limits (mh t) (nodeCount t + 1)
                            *** QED

{-@ h_to_log2H :: t : BTree a -> { ceilLog (nodeCount t + 1) == h t } @-}
h_to_log2H :: Tree a -> Proof
h_to_log2H (Nil) = ()
h_to_log2H t 
  | h t == mh t = ceilLog n == h t ? (pow_log2_equallity t) 
     === log2L (nodeCount t + 1) == h t ? mh_to_log2L t
     === mh t == h t *** QED 
  | h t == mh t + 1 = ceilLog n == h t ? (pow_log2_inequallity t) 
     === log2L (nodeCount t + 1) + 1 == h t ? mh_to_log2L t
     === mh t + 1 == h t *** QED 
  where 
    n = nodeCount t + 1

{-@ log_substract :: i : Nat -> l : { Nat | abs (i - l) <= 1 } -> { abs (log2L i - log2L l) <= 1 }  @-}
log_substract :: Int -> Int -> Proof
log_substract 0 0 = ()
log_substract 1 0 = ()
log_substract 0 1 = ()
log_substract 1 1 = ()
log_substract i l  = abs (log2L i - log2L l) <= 1
                      === abs (1 + log2L (div i 2) - 1 - log2L (div l 2)) <= 1
                      === abs (log2L (div i 2) - log2L (div l 2)) <= 1
                      ? log_substract (div i 2) (div l 2)
                      *** QED

{-@ log_substract2 :: i : { Nat | pow2 (log2L i) != i } -> l : { Nat | abs (i - l) <= 1 } -> { abs (log2L i + 1 - log2L l) <= 1 }  @-}
log_substract2 :: Int -> Int -> Proof
log_substract2 i l  
        | pow2 (log2L (div i 2)) /= (div i 2) = abs (log2L i + 1 - log2L l) <= 1
                      === abs (log2L (div i 2) + 2 - 1 - log2L (div l 2)) <= 1
                      === abs (1 + log2L (div i 2) - log2L (div l 2)) <= 1
                      ? log_substract2 (div i 2) (div l 2)
                      *** QED
        | otherwise = abs (log2L i + 1 - log2L l) <= 1
                      === abs (log2L (div i 2) + 2 - 1 - log2L (div l 2)) <= 1
                      === abs (1 + log2L (div i 2) - log2L (div l 2)) <= 1
                      === 1 <= 1
                      *** QED

{-@ lema_2_2 :: x : a -> l : BTree a -> r : { BTree a | abs (nodeCount l - nodeCount r) <= 1 }-> { balanced (Node x l r) } @-}
lema_2_2 :: (Eq a) => a -> Tree a -> Tree a -> Proof
lema_2_2 v l r 
    | pow2 (log2L (nodeCount l + 1)) == nodeCount l + 1&& h t == h l + 1 && mh t == mh l + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h l - mh l) <= 1 ? h_to_log2H l
              === abs (ceilLog (nodeCount l + 1) - mh l) <= 1 ? mh_to_log2L l 
              === abs (ceilLog (nodeCount l + 1) - log2L (nodeCount l + 1)) <= 1
              === abs (log2L (nodeCount l + 1) - log2L (nodeCount l + 1)) <= 1
              *** QED
    | pow2 (log2L (nodeCount l + 1)) == nodeCount l + 1 && h t == h l + 1 && mh t == mh r + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h l - mh r) <= 1 ? h_to_log2H l
              === abs (ceilLog (nodeCount l + 1) - mh r) <= 1 ? mh_to_log2L r 
              === abs (ceilLog (nodeCount l + 1) - log2L (nodeCount r + 1)) <= 1
              === abs (log2L (nodeCount l + 1) - log2L (nodeCount r + 1)) <= 1
              ? log_substract (nodeCount l + 1) (nodeCount r + 1)
              *** QED
    | pow2 (log2L (nodeCount r + 1)) == nodeCount r + 1 && h t == h r + 1 && mh t == mh l + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h r - mh l) <= 1 ? h_to_log2H r
              === abs (ceilLog (nodeCount r + 1) - mh l) <= 1 ? mh_to_log2L l 
              === abs (ceilLog (nodeCount r + 1) - log2L (nodeCount l + 1)) <= 1
              === abs (log2L (nodeCount r + 1) - log2L (nodeCount l + 1)) <= 1
              ? log_substract (nodeCount r + 1) (nodeCount l + 1)
              *** QED
    | pow2 (log2L (nodeCount r + 1)) == nodeCount r + 1 && h t == h r + 1 && mh t == mh r + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h r - mh r) <= 1 ? h_to_log2H r
              === abs (ceilLog (nodeCount r + 1) - mh r) <= 1 ? mh_to_log2L r 
              === abs (ceilLog (nodeCount r + 1) - log2L (nodeCount r + 1)) <= 1
              === abs (log2L (nodeCount r + 1) - log2L (nodeCount r + 1)) <= 1
              *** QED
    | pow2 (log2L (nodeCount l + 1)) /= nodeCount l + 1 && h t == h l + 1 && mh t == mh l + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h l - mh l) <= 1 ? h_to_log2H l
              === abs (ceilLog (nodeCount l + 1) - mh l) <= 1 ? mh_to_log2L l 
              === abs (ceilLog (nodeCount l + 1) - log2L (nodeCount l + 1)) <= 1
              === abs (log2L (nodeCount l + 1) + 1 - log2L (nodeCount l + 1)) <= 1
              *** QED
    | pow2 (log2L (nodeCount l + 1)) /= nodeCount l + 1 && h t == h l + 1 && mh t == mh r + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h l - mh r) <= 1 ? h_to_log2H l
              === abs (ceilLog (nodeCount l + 1) - mh r) <= 1 ? mh_to_log2L r 
              === abs (ceilLog (nodeCount l + 1) - log2L (nodeCount r + 1)) <= 1
              === abs (log2L (nodeCount l + 1) + 1 - log2L (nodeCount r + 1)) <= 1
              ? log_substract2 (nodeCount l + 1) (nodeCount r + 1)
              *** QED
    | pow2 (log2L (nodeCount r + 1)) /= nodeCount r + 1 && h t == h r + 1 && mh t == mh l + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h r - mh l) <= 1 ? h_to_log2H r
              === abs (ceilLog (nodeCount r + 1) - mh l) <= 1 ? mh_to_log2L l 
              === abs (ceilLog (nodeCount r + 1) - log2L (nodeCount l + 1)) <= 1
              === abs (log2L (nodeCount r + 1) + 1 - log2L (nodeCount l + 1)) <= 1
              ? log_substract2 (nodeCount r + 1) (nodeCount l + 1)
              *** QED
    | pow2 (log2L (nodeCount r + 1)) /= nodeCount r + 1 && h t == h r + 1 && mh t == mh r + 1 = balanced t 
              === abs (h t - mh t) <= 1
              === abs (h r - mh r) <= 1 ? h_to_log2H r
              === abs (ceilLog (nodeCount r + 1) - mh r) <= 1 ? mh_to_log2L r 
              === abs (ceilLog (nodeCount r + 1) - log2L (nodeCount r + 1)) <= 1
              === abs (log2L (nodeCount r + 1) + 1- log2L (nodeCount r + 1)) <= 1
              *** QED
  where
    t = Node v l r

{-@ lema_2_3 :: t : { Tree a  | braun t } -> { balanced t }@-}
lema_2_3 :: Tree a -> Proof
lema_2_3 (Nil) = ()
lema_2_3 t@(Node v l r) = balanced t 
        ? (
        (balanced l ? lema_2_3 l *** QED) 
        &&&
          (balanced r ? lema_2_3 r *** QED)
        &&& 
          (abs (h t - mh t) <= 1 ? lema_2_2 v l r 
          *** QED)
        )
        *** QED
{-
{-@ lema_2_4 :: t : BTree a -> t2 : { BTree a | nodeCount t <= nodeCount t2 } -> { h t <= h t2 }   @-}
lema_2_4 :: Tree a -> Tree a -> Proof
lema_2_4 Nil Nil = ()
lema_2_4 t t2 = h t <= h t2 ? h_to_log2H t
                === ceilLog (nodeCount t + 1) <= h t2 ? h_to_log2H t2
                === ceilLog (nodeCount t + 1) <= ceilLog (nodeCount t2 + 1)
                *** QED

-}
