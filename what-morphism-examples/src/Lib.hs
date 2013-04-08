--------------------------------------------------------------------------------
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
module Lib where


--------------------------------------------------------------------------------
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
