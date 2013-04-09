--------------------------------------------------------------------------------
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
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
listSum :: List Int -> Int
listSum Empty       = 0
listSum (Cons x xs) = x + listSum xs


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
main :: IO ()
main = do
    print $ listSum testList
    print $ listMap (+ 1) testList
    print $ listFilter odd testList
    print $ treeSum testTree
    print $ treeMap (+ 1) testTree
