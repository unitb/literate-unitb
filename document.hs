module Document where

import Data.Char
import Data.IORef

import System.IO
import System.IO.Unsafe

extract_doc xs = do
        let p  = filter (\x -> take 2 x == "> " || take 2 x == ">\t")
        let ls = (map (drop 2) $ p $ lines xs)
        putStrLn $ unlines ls

data Section = Section String [String]
    deriving Show

prefix xs ys = xs == take (length xs) ys

data DocPart = Head String | Line String | Trash

keywords = unsafePerformIO $ newIORef [
    "proof",
    "event",
    "machine",
    "invariant",
    "property",
    "element",
    "variable",
    "variables",
    "transient" ]

extract_struct xs = do
        kw <- readIORef keywords
        let ys = map (".." ++) kw
        let ls = lines xs
        let zs = map (f ys) ls ++ [Trash]
        let ws = reverse $ fst $ foldl g ([], Nothing) zs
        return ws
    where
        f kw x
            | any (\y -> prefix y x) kw      = Head x
            | prefix "\t" x || all isSpace x = Line x
            | otherwise                      = Trash
        g x y                             = (sect x y, osect x y)
        sect (xs, Just (x, ys)) (Line s)  = xs
        sect (xs, Nothing) _              = xs
        sect (xs, Just (x, ys)) _         = (Section x $ reverse ys):xs
        osect (xs, _) (Head s)            = Just (drop 2 s, [])
        osect (xs, Just (x, ys)) (Line s) = Just (x, (drop 1 s):ys)
        osect _ _                         = Nothing
        
 

main = do
        xs <- readFile "doc.lit"
        extract_doc xs
        extract_struct xs