module Latex.Scanner where

import Control.Monad
import Control.Monad.Instances

data State a = State [(a,(Int,Int))] Int Int

data Scanner a b = 
    Scanner (State a -> Either (String, Int, Int) (b, State a))

--instance Monad (Either a) where
--    return        = Right
--    Right b >>= f = f b
--    Left a >>= _  = Left a

instance Monad (Scanner a) where
    f >>= gF = comb f gF
    fail s   = Scanner (\(State _ i j) -> Left (s, i, j))
    return x = Scanner (\s -> Right (x,s))
    
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
                Left xs ->
                    fl x

pick :: [(Scanner a b, b -> Scanner a c)] -> Scanner a c -> Scanner a c
pick [] x = x
pick ((a,b):xs) y = try a b $ pick xs y

read_if :: (a -> Bool) -> (a -> Scanner a b) -> Scanner a b -> Scanner a b
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

line_number xs     = concatMap f ys
    where
        f (n, xs)  = map (g n) xs
        g n (i, x) = (x, (n, i))
        ys         = zip [1..] $ map (zip [1..] . (++ "\n")) $ lines xs

peek = Scanner f
    where
        f s@(State xs _ _) = Right (map fst xs, s)

eof = do
        b <- is_eof
        if b 
            then return ()
            else fail "Expected end of file"
            
is_eof = do
        xs <- peek
        return (null xs)
            
read_char = Scanner f
    where
        f s@(State ((x,(i,j)):xs) _ _) = Right (x, State xs i j)
        f s@(State [] i j)             = Left ("Expected: character", i, j)

read_string :: Int -> Scanner a [a]
read_string 0 = return []
read_string n = do
        x  <- read_char
        xs <- read_string (n-1)
        return (x:xs)

match :: ([a] -> Maybe Int) -> Scanner a (Maybe [a])
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

match_first :: [Pattern a b] -> Scanner a b -> Scanner a b
match_first [] x       = x
match_first ((p,f):xs) x = do
        c <- match p
        case c of
            Just ys -> f ys
            Nothing -> match_first xs x

read_lines :: Scanner Char a -> String -> Either (String, Int, Int) a 
read_lines s xs = read_tokens s (line_number xs)

read_tokens :: Scanner a b -> [(a, (Int,Int))] -> Either (String, Int, Int) b
read_tokens (Scanner f) xs = 
        do  (r, State xs i j) <- f (State xs 0 0)
            case xs of 
                [] -> return r
                _ -> Left ("expected end of input", i, j)
        

choice :: [Scanner a b] -> Scanner a c -> (b -> Scanner a c) -> Scanner a c
choice [] f s = f
choice (x:xs) f s = try x s (choice xs f s)
--    where
--        g s0 = 
--            case h s0 of
--                    Left  _ -> 
--                        case choice xs d of
--                            Scanner h2 -> 2h s0
--                    x -> x

get_line_info :: Scanner a (Int, Int)
get_line_info = Scanner f
    where
        f s@(State _ i j) = Right ((i,j), s)

sep :: Scanner a b -> Scanner a c -> Scanner a [b]
sep b s = do
            try s 
                (\x -> do
                    x  <- b
                    xs <- sep b s
                    return (x:xs)) 
                (return [])

sep1 :: Scanner a b -> Scanner a c -> Scanner a [b]
sep1 b s = do
        x <- b
        xs <- sep b s
        return (x:xs)

sepBy :: Scanner a b -> Scanner a c -> Scanner a [(c,b)] 
sepBy b s = do
            try s 
                (\x -> do
                    y  <- b
                    xs <- sepBy b s
                    return ((x,y):xs)) 
                (return [])

sepBy1 :: Scanner a b -> Scanner a c -> Scanner a (b,[(c,b)]) 
sepBy1 b s = do
        x <- b
        xs <- sepBy b s
        return (x,xs)

look_ahead :: Scanner a b -> Scanner a Bool
look_ahead (Scanner f) = Scanner g
    where
        g x = case f x of
                Right _ -> Right (True,x)
                Left  _ -> Right (False,x)

read_ :: String -> Scanner Char ()
read_ xs = do
        x <- match $ match_string xs
        case x of
            Just _  -> return ()
            Nothing -> fail ("expecting: " ++ xs)