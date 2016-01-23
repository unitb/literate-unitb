{-# LANGUAGE IncoherentInstances #-}
module Utilities.Format 
    ( format, Formatter, fargs, substAll
    ) 
where

format :: Formatter a => String -> a
format xs = fargs xs 0

class Formatter a where
    fargs :: String -> Int -> a

instance Formatter [Char] where
    fargs xs _ = xs

instance (Show a, Formatter b) => Formatter (a -> b) where
    fargs xs n x = fargs (subst xs n $ show x) (n+1)

instance Formatter a => Formatter ([Char] -> a) where
    fargs xs n x = fargs (subst xs n x) (n+1)

subst :: String -> Int -> String -> String
subst [] _ _ = []
subst xs n z
        | take m xs == fn   = z ++ subst (drop m xs) n z
        | otherwise         = take 1 xs ++ subst (drop 1 xs) n z
    where
        fn = "{" ++ show n ++ "}"
        m = length fn

substAll :: String -> [String] -> String
substAll xs ys = foldl (uncurry <$> subst) xs $ zip [0..] ys
