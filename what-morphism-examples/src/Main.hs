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
treeUpTo :: Int -> Int -> Tree Int
treeUpTo lo hi
    | lo >= hi  = Leaf lo
    | otherwise =
        let mid = (lo + hi) `div` 2
        in Node (treeUpTo lo mid) (treeUpTo (mid + 1) hi)


--------------------------------------------------------------------------------
treeUpTo' :: Integral a => a -> a -> Tree [a]
treeUpTo' lo hi
    | lo >= hi  = Leaf [lo]
    | otherwise =
        let mid = (lo + hi) `div` 2
        in Node (treeUpTo' lo mid) (treeUpTo' (mid + 1) hi)


--------------------------------------------------------------------------------
treeUpTo'' :: Integral a => a -> a -> Tree [a]
treeUpTo'' lo' hi' = buildTree (\leaf node ->
    let g lo hi
            | lo >= hi  = leaf [lo]
            | otherwise =
                let mid = (lo + hi) `div` 2
                in node (g lo mid) (g (mid + 1) hi)
    in g lo' hi')
{-# NOINLINE treeUpTo'' #-}


--------------------------------------------------------------------------------
treeSum :: Tree Int -> Double
treeSum (Leaf x)   = fromIntegral x
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
haskellUpTo :: Int -> Int -> [Int]
haskellUpTo lo up = go lo
  where
    go i
        | i > up    = []
        | otherwise = i : go (i + 1)


--------------------------------------------------------------------------------
haskellSum :: [Int] -> Double
haskellSum []       = fromIntegral (0 :: Int)
haskellSum (x : xs) = fromIntegral x + haskellSum xs


--------------------------------------------------------------------------------
type Haskell a = [a]
$(deriveFold ''[] "foldHaskell")
$(deriveBuild ''[] "buildHaskell")
{-# ANN type Haskell (RegisterFoldBuild "foldHaskell" "buildHaskell") #-}


--------------------------------------------------------------------------------
mkTreeBuild :: Int -> Tree Int
mkTreeBuild = \n -> buildTree $ \leaf node ->
    let g lo hi
            | lo >= hi  = leaf lo
            | otherwise =
                let mid = (lo + hi) `div` 2
                in node (g lo mid) (g (mid + 1) hi)
    in g 1 n


--------------------------------------------------------------------------------
treeSumFold :: Int -> Tree Int -> Int -> Double
treeSumFold = \a t b -> foldTree (\x -> fromIntegral (x + a + b)) (+) t


--------------------------------------------------------------------------------
foldBuild :: Double
foldBuild =
    ((\a t b -> foldTree (\x -> fromIntegral (x + a + b)) (+) t)
        1
        ((\n -> buildTree $ \leaf node ->
            let g lo hi
                    | lo >= hi  = leaf lo
                    | otherwise =
                        let mid = (lo + hi) `div` 2
                        in node (g lo mid) (g (mid + 1) hi)
            in g 1 n)
            10)
        5)


--------------------------------------------------------------------------------
foldBuildFused :: Double
foldBuildFused =
    (\a t b ->
        ((\n -> (\leaf node ->
            let g lo hi
                    | lo >= hi  = leaf lo
                    | otherwise =
                        let mid = (lo + hi) `div` 2
                        in node (g lo mid) (g (mid + 1) hi)
            in g 1 n))
            10) (\x -> fromIntegral (x + a + b)) (+))
        1
        undefined
        5


--------------------------------------------------------------------------------
foldBuildInlined :: Double
foldBuildInlined = (treeSumFold 1 (mkTreeBuild 10) 5)


--------------------------------------------------------------------------------
mkResult :: Int -> Double
mkResult n = treeSum (treeMap (+ 1) (1 `treeUpTo` n))


--------------------------------------------------------------------------------
hresult :: Double
hresult = haskellSum (1 `haskellUpTo` 10)


--------------------------------------------------------------------------------
jiggle :: [String] -> Int -> [String]
jiggle = \ds b -> case ds of
    []       -> [];
    (y : ys) -> case b <= 1 of
        False -> y : jiggle ys (b - 1)
        True -> y : []


--------------------------------------------------------------------------------
main :: IO ()
main = do
    {-
    defaultMain
    [ bench "10 nodes"     $ nf mkResult 10
    , bench "100 nodes"    $ nf mkResult 100
    , bench "1000 nodes"   $ nf mkResult 1000
    , bench "10000 nodes"  $ nf mkResult 10000
    , bench "100000 nodes" $ nf mkResult 100000
    ]
    -}
    print hresult
    print (mkResult 100)
    -- let ls = [1 .. 10]  -- (1 `haskellUpTo` 10)
    -- print ls
    -- print (haskellSum ls)
    -- print $ foldBuild
    -- print $ treeUpTo' 1 (10 :: Integer)
    -- print $ treeUpTo'' 1 (10 :: Integer)
    -- print $ jiggle ["lol"] 3
