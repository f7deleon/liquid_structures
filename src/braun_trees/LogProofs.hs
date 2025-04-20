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

{-@ node_count_max :: t :  BTree a -> { nodeCount t <= pow2 (h t) - 1} @-}
node_count_max :: Tree a -> Proof
node_count_max (Nil) = ()
node_count_max t@(Node _ Nil Nil) = ()
node_count_max t@(Node _ l r) 
      | h l >= h r && nodeCount l >= nodeCount r = nodeCount t  <= pow2 (h t) - 1
                  === 1 + nodeCount l + nodeCount r <= pow2 (1 + h l) - 1
                  === 1 + nodeCount l + nodeCount r <= 2 * pow2 (h l) - 1 
                  ? (1 + nodeCount l + nodeCount r <=  1 + nodeCount l + nodeCount l) 
                  ? (
                      nodeCount l + nodeCount l + 1 <= 2 * pow2 (h l) - 1
                      === 2 * nodeCount l <= 2 * pow2 (h l) - 2
                      === nodeCount l <= pow2 (h l) - 1
                      ? node_count_max l
                      *** QED)
                  *** QED
      | h l < h r && nodeCount l <= nodeCount r = nodeCount t  <= pow2 (h t) - 1
                  === 1 + nodeCount l + nodeCount r <= pow2 (1 + h r) - 1
                  === 1 + nodeCount l + nodeCount r <= 2 * pow2 (h r) - 1 
                  ? (1 + nodeCount l + nodeCount r <= 1 + nodeCount r + nodeCount r) 
                  ? (
                      nodeCount r + nodeCount r + 1 <= 2 * pow2 (h r) - 1
                      === 2 * nodeCount r <= 2 * pow2 (h r) -2
                      === nodeCount r <= pow2 (h r) - 1
                      ? node_count_max r
                      *** QED)
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
node_count_min t@(Node _ Nil Nil) = ()
node_count_min t@(Node _ Nil r) = ()
node_count_min t@(Node _ l Nil) = ()
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
                                                ? hm_node_count_limits2 l *** QED)
                                                *** QED
  | mh l >= mh r && nodeCount l <= nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === 2 + nodeCount l + nodeCount r < pow2 (mh t + 1) 
                                                ? (2 + nodeCount l + nodeCount r <= 2 + nodeCount r + nodeCount r)
                                                ? (2 + 2 * nodeCount r < pow2 (mh r + 2)
                                                === nodeCount r + 1 < pow2 (mh r + 1)
                                                ? hm_node_count_limits2 r *** QED)
                                                *** QED
  | mh l < mh r && nodeCount l < nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === nodeCount t + 1 < pow2 (mh t + 1)
                                                ? hm_node_count_limits2 t
                                                *** QED
  | mh l >= mh r && nodeCount l > nodeCount r = nodeCount t + 1 < pow2 (h t) 
                                                === nodeCount t + 1 < pow2 (mh t + 1)
                                                ? hm_node_count_limits2 t
                                                *** QED

{-@ hm_node_count_limits2 :: t : BTree a -> { nodeCount t + 1 < pow2 (mh t + 1)} @-}
hm_node_count_limits2 :: Tree a -> Proof
hm_node_count_limits2 (Nil) = nodeCount (Nil) + 1 < pow2 (mh Nil + 1) === 1 < pow2 (0 + 1) === 1 < 2 *** QED
hm_node_count_limits2 t@(Node _ l r) 
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

{-@ hm_to_log2L :: t : BTree a -> { log2L (nodeCount t + 1) == mh t } @-}
hm_to_log2L :: Tree a -> Proof
hm_to_log2L (Nil) = ()
hm_to_log2L t@(Node _ Nil Nil) = log2L (nodeCount t + 1) == mh t === log2L (2) == 1 === 1 == 1 *** QED
hm_to_log2L t@(Node _ l r) = log2L (nodeCount t + 1) == mh t 
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
                                  ? hm_node_count_limits2 (t)
                                  *** QED
                                )
                              ***QED
                            )
                            ? log_limits (mh t) (nodeCount t + 1)
                            *** QED

{-@ hm_to_log2H :: t : BTree a -> { ceilLog (nodeCount t + 1) == h t } @-}
hm_to_log2H :: Tree a -> Proof
hm_to_log2H (Nil) = ()
hm_to_log2H t@(Node _ l r) 
  | h t == mh t = ceilLog n == h t ? 
    (pow2 (log2L (n)) == n  ? hm_to_log2L t
      === pow2 (mh t) == nodeCount t + 1
      === log2L (pow2 (mh t)) == log2L (nodeCount t + 1) ? log_identity (mh t)
      === mh t == log2L (nodeCount t + 1) ? hm_to_log2L t
      === log2L n == log2L n *** QED)
      === log2L n == h t ? hm_to_log2L t
      === mh t == h t *** QED 
  | h t /= mh t = ceilLog n == h t ? 
    (pow2 (log2L (n)) /= n  ? hm_to_log2L t
      === pow2 (mh t) /= nodeCount t + 1
      
      === mh t /= mh t *** QED)
      === log2L n == h t ? 
where 
    n = nodeCount t + 1


