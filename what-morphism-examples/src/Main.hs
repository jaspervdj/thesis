--------------------------------------------------------------------------------
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
import           WhatMorphism.Annotations
import           WhatMorphism.TemplateHaskell


--------------------------------------------------------------------------------
data List a
    = Cons a (List a)
    | Empty
    deriving (Show)


--------------------------------------------------------------------------------
$(deriveFold ''List "foldList")
$(deriveBuild ''List "buildList")
{-# ANN type List (RegisterFoldBuild 'foldList 'buildList) #-}
{-# RULES "foldList/buildList"
    forall (g :: forall b. (a -> b -> b) -> b -> b) c n.
    foldList c n (buildList g) = g c n #-}


--------------------------------------------------------------------------------
data Tree a
    = Leaf a
    | Node (Tree a) (Tree a)
    deriving (Show)


--------------------------------------------------------------------------------
$(deriveFold ''Tree "foldTreeHerp")
$(deriveBuild ''Tree "buildTree")


--------------------------------------------------------------------------------
listSum :: List Int -> Int
listSum Empty       = 0
listSum (Cons x xs) = x + listSum xs


--------------------------------------------------------------------------------
foldListTest :: Int
foldListTest = foldList (+) 0 buildListTest


--------------------------------------------------------------------------------
buildListTest :: List Int
buildListTest = buildList $ \cons nil ->
    cons 4 $ cons 3 $ cons 2 $ cons 1 nil


--------------------------------------------------------------------------------
foldTreeTest :: Int
foldTreeTest = foldTreeHerp id (+) buildTreeTest


--------------------------------------------------------------------------------
buildTreeTest :: Tree Int
buildTreeTest = buildTree $ \leaf node ->
    node
        (leaf 2)
        (node
            (leaf 7)
            (leaf 8))


--------------------------------------------------------------------------------
main :: IO ()
main = do
    print $ foldTreeTest
    print $ listSum Empty
