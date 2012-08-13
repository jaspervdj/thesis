foo :: Int -> Int
foo x = x + 4

main :: IO ()
main = putStrLn $ show $ foo 7
