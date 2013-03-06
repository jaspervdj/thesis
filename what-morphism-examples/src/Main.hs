--------------------------------------------------------------------------------
{-# LANGUAGE RankNTypes #-}
module Main where


--------------------------------------------------------------------------------
main :: IO ()
main = putStrLn "Hello world!"


--------------------------------------------------------------------------------
sum1 :: [Int] -> Int
sum1 []       = 0
sum1 (x : xs) = x + sum1 xs


--------------------------------------------------------------------------------
-- | Kind of like sum, but we do some nasty scoping trick I guess
scope :: [Int] -> Int
scope []       = 0
scope (x : xs) = x + scope xs + length xs


--------------------------------------------------------------------------------
map1 :: (a -> b) -> [a] -> [b]
map1 _ []       = []
map1 f (x : xs) = f x : map1 f xs


--------------------------------------------------------------------------------
filter1 :: (a -> Bool) -> [a] -> [a]
filter1 _ []       = []
filter1 p (x : xs)
    | p x          = x : filter1 p xs
    | otherwise    = filter1 p xs


--------------------------------------------------------------------------------
mean :: [Double] -> Double
mean xs =
    let len  = foldr (const (+ 1)) 0 xs
        sum' = foldr (+)           0 xs
    in sum' / len


--------------------------------------------------------------------------------
-- | This example shows why fold-fold fusion might not be so useful after all
qux :: [Double] -> Double
qux xs =
    let len  = foldr (const (+ 1)) 0 xs
        sum' = foldr (+)           0 xs
    in case len of
        3 -> 42
        _ -> sum' / len
