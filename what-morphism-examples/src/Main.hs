--------------------------------------------------------------------------------
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
import           WhatMorphism.Annotations
import           WhatMorphism.TemplateHaskell



--------------------------------------------------------------------------------
import           Lib


--------------------------------------------------------------------------------
testList :: List Int
testList = buildList $ \c n ->
    let g x | x > 100   = n
            | otherwise = c x (g (x + 1))
    in g 1


--------------------------------------------------------------------------------
listUpTo :: Int -> Int -> List Int
listUpTo k n
    | k >= n    = Cons k Empty
    | otherwise = Cons k (listUpTo (k + 1) n)
{-# INLINE [2] listUpTo #-}


--------------------------------------------------------------------------------
listSum :: List Int -> Int
listSum Empty       = 0
listSum (Cons x xs) = x + listSum xs
{-# INLINE [2] listSum #-}


--------------------------------------------------------------------------------
listSumWith :: List Int -> Int -> Int
listSumWith Empty       c = c
listSumWith (Cons x xs) c = x + listSumWith xs c


--------------------------------------------------------------------------------
listFilter :: (a -> Bool) -> List a -> List a
listFilter _ Empty = Empty
listFilter f (Cons x xs)
    | f x          = Cons x (listFilter f xs)
    | otherwise    = listFilter f xs


--------------------------------------------------------------------------------
listMap :: (a -> b) -> List a -> List b
listMap _ Empty       = Empty
listMap f (Cons x xs) = Cons (f x) (listMap f xs)


--------------------------------------------------------------------------------
testTree :: Tree Int
testTree = buildTree $ \leaf node ->
    let mkTree lo hi
            | lo >= hi  = leaf lo
            | otherwise =
                let mid = (lo + hi) `div` 2
                in node (mkTree lo mid) (mkTree (mid + 1) hi)
    in mkTree 1 1024


--------------------------------------------------------------------------------
treeSum :: Tree Int -> Int
treeSum (Leaf x)   = x
treeSum (Node l r) = treeSum l + treeSum r


--------------------------------------------------------------------------------
treeMap :: (a -> b) -> Tree a -> Tree b
treeMap f (Leaf x)   = Leaf (f x)
treeMap f (Node l r) = Node (treeMap f l) (treeMap f r)


--------------------------------------------------------------------------------
treeMapB :: forall a b. (a -> b) -> Tree a -> Tree b
treeMapB f' tree' = buildTree (\(leaf :: b -> c) (node :: c -> c -> c) ->
    let g :: (a -> b) -> Tree a -> c
        g f (Leaf x)   = leaf (f x)
        g f (Node l r) = node (g f l) (g f r)
    in g f' tree')
{-# NOINLINE treeMapB #-}


--------------------------------------------------------------------------------
result :: Int
result = listSum (1 `listUpTo` 10)
{-# NOINLINE result #-}


--------------------------------------------------------------------------------
main :: IO ()
main = print result
