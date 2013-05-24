--------------------------------------------------------------------------------
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
import           Criterion                    (bench, nf)
import           Criterion.Main               (defaultMain)
import           WhatMorphism.Annotations
import           WhatMorphism.HaskellList
import           WhatMorphism.TemplateHaskell



--------------------------------------------------------------------------------
import           Lib


--------------------------------------------------------------------------------
sumt :: Tree Int -> Int
sumt (Leaf x)   = x
sumt (Node l r) = sumt l + sumt r


--------------------------------------------------------------------------------
mapt :: (a -> b) -> Tree a -> Tree b
mapt f = go
  where
    go (Leaf x)   = Leaf (f x)
    go (Node l r) = Node (go l) (go r)


--------------------------------------------------------------------------------
uptot :: Int -> Int -> Tree Int
uptot = go
  where
    go lo hi
        | lo >= hi  = Leaf lo
        | otherwise =
            let mid = (lo + hi) `div` 2
            in Node (go lo mid) (go (mid + 1) hi)
{-# INLINE uptot #-}


--------------------------------------------------------------------------------
t1, t2, t3, t4, t5 :: Int -> Int
t1 n = sumt (1 `uptot` n)
t2 n = sumt (mapt (+ 1) (1 `uptot` n))
t3 n = sumt (mapt (+ 1) (mapt (+ 1) (1 `uptot` n)))
t4 n = sumt (mapt (+ 1) (mapt (+ 1) (mapt (+ 1) (1 `uptot` n))))
t5 n = sumt (mapt (+ 1) (mapt (+ 1) (mapt (+ 1) (mapt (+ 1) (1 `uptot` n)))))


--------------------------------------------------------------------------------
suml :: [Int] -> Int
suml []       = 0
suml (x : xs) = x + suml xs


--------------------------------------------------------------------------------
mapl :: (a -> b) -> [a] -> [b]
mapl f = go
  where
    go []       = []
    go (x : xs) = f x : go xs


--------------------------------------------------------------------------------
uptol :: Int -> Int -> [Int]
uptol lo up = go lo
  where
    go i
        | i > up    = []
        | otherwise = i : go (i + 1)
{-# INLINE uptol #-}


--------------------------------------------------------------------------------
l1, l2, l3, l4, l5 :: Int -> Int
l1 n = suml (1 `uptol` n)
l2 n = suml (mapl (+ 1) (1 `uptol` n))
l3 n = suml (mapl (+ 1) (mapl (+ 1) (1 `uptol` n)))
l4 n = suml (mapl (+ 1) (mapl (+ 1) (mapl (+ 1) (1 `uptol` n))))
l5 n = suml (mapl (+ 1) (mapl (+ 1) (mapl (+ 1) (mapl (+ 1) (1 `uptol` n)))))


--------------------------------------------------------------------------------
main :: IO ()
main = defaultMain
    [ bench "t1" $ nf t1 100000
    , bench "t2" $ nf t2 100000
    , bench "t3" $ nf t3 100000
    , bench "t4" $ nf t4 100000
    , bench "t5" $ nf t5 100000

    , bench "l1" $ nf l1 100000
    , bench "l2" $ nf l2 100000
    , bench "l3" $ nf l3 100000
    , bench "l4" $ nf l4 100000
    , bench "l5" $ nf l5 100000
    ]
