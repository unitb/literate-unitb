module Latex.Scanner 
    ( read_lines, read_tokens
    , is_eof, peek, read_char
    , get_line_info, Scanner(..)
    , match_first, match_string
    , look_ahead, try, choice
    , read_if, match, many
    , line_number
    , sep1,sep )
where

import Control.Monad

import Data.Maybe
import qualified Data.List.NonEmpty as NE
import Data.String.Lines as L

import Utilities.Syntactic

data State a = State [(a,LineInfo)] LineInfo

data Scanner a b = 
    Scanner (State a -> Either [Error] (b, State a))

instance Functor (Scanner a) where
    fmap = liftM

instance Applicative (Scanner a) where
    f <*> x = ap f x
    pure x  = return x

instance Monad (Scanner a) where
    f >>= gF = comb f gF
    fail s   = raise . Error s =<< get_line_info
    return x = Scanner (\s -> Right (x,s))

raise :: Error -> Scanner a k
raise e = Scanner (\_ -> Left [e])

comb :: Scanner a b -> (b -> Scanner a c) -> Scanner a c
comb (Scanner f) gF = Scanner h
    where
        h s0               = h0 (f s0)
        h0 (Left x)        = Left x
        h0 (Right (r, s1)) = g s1
            where
                Scanner g  = gF r

try :: Scanner a b -> (b -> Scanner a c) -> Scanner a c -> Scanner a c
try (Scanner bl) sc (Scanner fl) = Scanner ret
    where
        ret x = 
            case bl x of
                Right (y, s) -> 
                    case sc y of
                        Scanner f -> f s
                Left _ ->
                    fl x


read_if :: Token a => (a -> Bool) -> (a -> Scanner a b) -> Scanner a b -> Scanner a b
read_if p left right = do
        b <- is_eof
        if b then right
        else do
            x:_ <- peek 
            if p x
            then do
                read_char
                left x
            else
                right

line_number :: String -> String -> [(Char, LineInfo)]
line_number fn xs     = concatMap f ys
    where
        f (n, xs)  = map (g n) xs
        g n (i, x) = (x, LI fn n i)
        ys         = zip [1..] $ map (zip [1..]) $ NE.toList $ L.lines' xs
        --addEOL = maybe [] (uncurry (++) . (second (:[]))) . unconsR
        --ys         = zip [1..] $ map (zip [1..] . (++ "\n")) $ lines xs

--unconsR :: [a] -> Maybe ([a],a)
--unconsR xs 
--    | null xs   = Nothing
--    | otherwise = Just (init xs,last xs)

peek :: Scanner a [a]
peek = Scanner f
    where
        f s@(State xs _) = Right (map fst xs, s)

            
is_eof :: Scanner a Bool
is_eof = do
        xs <- peek
        return (null xs)
            
read_char :: Token b => Scanner b b
read_char = Scanner f
    where
        f (State (t@(x,_):xs) _) 
            = Right (x, State xs $ end t)
        f (State [] li)               
            = Left [(Error "Expected: character" li)]

read_string :: Token a => Int -> Scanner a [a]
read_string 0 = return []
read_string n = do
        x  <- read_char
        xs <- read_string (n-1)
        return (x:xs)

match :: Token a => ([a] -> Maybe Int) -> Scanner a (Maybe [a])
match p = do
        xs <- peek
        case p xs of
            Just n  -> do
                xs <- read_string n
                return $ Just xs
            Nothing -> return Nothing

match_string :: Eq a => [a] -> [a] -> Maybe Int
match_string xs = \ys -> do
        guard (xs == take n ys)
        return n
    where
        n = length xs

type Pattern a b = ([a] -> Maybe Int, [a] -> Scanner a b)

match_first :: Token a => [Pattern a b] -> Scanner a b -> Scanner a b
match_first [] x       = x
match_first ((p,f):xs) x = do
        c <- match p
        case c of
            Just ys -> f ys
            Nothing -> match_first xs x

read_lines :: Scanner Char a 
           -> FilePath -> String 
           -> Either [Error] a 
read_lines s fn xs = read_tokens s (line_number fn xs) $ LI fn 1 1

read_tokens :: Scanner a b
            -> [(a, LineInfo)] 
            -> LineInfo
            -> Either [Error] b
read_tokens (Scanner f) xs (LI fn i j) = 
        do  li <- case xs of 
                (_,li):_ -> return li
                _ -> return (LI fn i j)
            (r, State xs li) <- f (State xs li)
            case xs of 
                [] -> return r
                _ -> Left [(Error "expected end of input" li)]
        

choice :: [Scanner a b] -> Scanner a c -> (b -> Scanner a c) -> Scanner a c
choice [] f _ = f
choice (x:xs) f s = try x s (choice xs f s)


get_line_info :: Scanner a LineInfo
get_line_info = Scanner f
    where
        f s@(State _ li) = Right (li, s)


many :: Scanner a b -> Scanner a [b]
many p = do
        try p
            (\x -> do
                xs <- many p
                return (x:xs))
            (return [])

sep :: Scanner a b -> Scanner a c -> Scanner a [b]
sep b s = do
        try s 
            (\_ -> do
                x  <- b
                xs <- sep b s
                return (x:xs)) 
            (return [])

sep1 :: Scanner a b -> Scanner a c -> Scanner a [b]
sep1 b s = do
        x <- b
        xs <- sep b s
        return (x:xs)


look_ahead' :: Scanner a b -> Scanner a (Maybe b)
look_ahead' (Scanner f) = Scanner g
    where
        g x = case f x of
                Right (y,_) -> Right (Just y,x)
                Left  _ -> Right (Nothing,x)

look_ahead :: Scanner a b -> Scanner a Bool
look_ahead cmd = isJust `liftM` look_ahead' cmd

            
