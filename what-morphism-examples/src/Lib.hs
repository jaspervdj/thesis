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
{-# ANN type List (RegisterFoldBuild "foldList" "buildList") #-}


--------------------------------------------------------------------------------
data Tree a
    = Leaf a
    | Node (Tree a) (Tree a)
    deriving (Show)


--------------------------------------------------------------------------------
$(deriveFold ''Tree "foldTree")
{-# NOINLINE foldTree #-}
$(deriveBuild ''Tree "buildTree")
{-# NOINLINE buildTree #-}
{-# ANN type Tree (RegisterFoldBuild "foldTree" "buildTree") #-}
