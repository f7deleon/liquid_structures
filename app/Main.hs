{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--reflect" @-}
{-@ LIQUID "--ple" @-}
{-# OPTIONS_GHC -XPackageImports #-}
{-# LANGUAGE GADTs #-}

module Main where

import Criterion.Main
-- import Type.BST
-- import LiquidList

main :: IO ()
main = defaultMain []
-- main = defaultMain [
--   bgroup "External ABB " [ bench "100 elements"  $ whnf makeTreeFromList [1..100]
--                , bench "500 elements"  $ whnf makeTreeFromList [1..500]
--                , bench "1000 elements"  $ whnf makeTreeFromList [1..1000]
--                , bench "10000 elements" $ whnf makeTreeFromList [1..10000]
--                , bench "100000 elements" $ whnf makeTreeFromList [1..100000]
--                , bench "1000000 elements" $ whnf makeTreeFromList [1..1000000]
--                ],
--   bgroup "Internal ABB " [ bench "100 elements"  $ whnf makeSimpleABB [1..100]
--                , bench "500 elements"  $ whnf makeSimpleABB [1..500]
--                , bench "1000 elements"  $ whnf makeSimpleABB [1..1000]
--                , bench "10000 elements" $ whnf makeSimpleABB [1..10000]
--                , bench "100000 elements" $ whnf makeSimpleABB [1..100000]
--                , bench "1000000 elements" $ whnf makeSimpleABB [1..1000000]
--                ],                     
--   bgroup "Simple ABB " [ bench "100 elements"  $ whnf makeSimpleABB [1..100]
--                , bench "500 elements"  $ whnf makeSimpleABB [1..500]
--                , bench "1000 elements"  $ whnf makeSimpleABB [1..1000]
--                , bench "10000 elements" $ whnf makeSimpleABB [1..10000]
--                , bench "100000 elements" $ whnf makeSimpleABB [1..100000]
--                , bench "1000000 elements" $ whnf makeSimpleABB [1..1000000]
--                ],
--   bgroup "Dependent type ABB " [ bench "100 elements"  $ whnf fromlist [1..100]
--                , bench "500 elements"  $ whnf fromlist [1..500]
--                , bench "1000 elements"  $ whnf fromlist [1..1000]
--                , bench "10000 elements" $ whnf fromlist [1..10000]
--                , bench "100000 elements" $ whnf fromlist [1..100000]
--                , bench "1000000 elements" $ whnf fromlist [1..1000000]
--                ]                  
--   ]
