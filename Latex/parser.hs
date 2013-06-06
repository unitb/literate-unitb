module Latex.Parser where

import Control.Monad

import Data.Char
import Data.Map hiding ( map, null )

--import Text.ParserCombinators.ReadP

data LatexDoc = 
        Env String [[LatexDoc]] [LatexDoc]
        | Bracket Bool [LatexDoc]
        | Text [LatexToken]
    deriving (Eq)

data LatexToken =
        Command String
        | TextBlock String
        | Blank String
        | Open Bool | Close Bool
    deriving (Eq, Show)
    
instance Show LatexDoc where
    show (Env b _ xs) = "Env{" ++ b ++ "} (" ++ show (length xs) ++ ")"
    show (Text xs)    = "Text (" ++ show (take 10 xs) ++ "...)"
    show (Bracket True c) = "Bracket {" ++ show c ++ "} "
    show (Bracket False c) = "Bracket [" ++ show c ++ "] "

source (Text xs) = concatMap lexeme xs
source x         = show x

lexeme (Command xs)   = xs
lexeme (TextBlock xs) = xs
lexeme (Blank xs)     = xs
lexeme (Open b)
    | b               = "{"
    | not b           = "["
lexeme (Close b)
    | b               = "}"
    | not b           = "]"

begin_kw = "\\begin"
end_kw   = "\\end"

data State a = State [(a,(Int,Int))] Int Int

data Scanner a b = 
    Scanner (State a -> Either (String, Int, Int) (b, State a))

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

type Pattern a b = ([a] -> Maybe Int, [a] -> b)

match_first :: [Pattern a b] -> Scanner a (Maybe b)
match_first []     = return Nothing
match_first ((p,f):xs) = do
        c <- match p
        case c of
            Just ys -> return $ Just $ f ys
            Nothing -> match_first xs

is_identifier :: String -> Maybe Int
is_identifier []    = Nothing
is_identifier (x:xs)
    | isAlpha x     = Just (1 + length (takeWhile isAlphaNum xs))
    | otherwise     = Nothing 

is_command []       = Nothing
is_command (x:xs)   
    | x == '\\'     =
                (do n <- is_identifier xs
                    return (n+1)) `mplus`
                (do guard (not $ null xs)
                    if isSymbol $ head xs
                        then return 2
                        else Nothing)
    | otherwise     = Nothing

is_space :: String -> Maybe Int
is_space xs = do
        let n = length $ takeWhile isSpace xs
        guard (1 <= n)
        Just n

line_info = Scanner f
    where
        f s@(State _ i j) = Right ((i,j), s)

tex_tokens :: Scanner Char [(LatexToken,(Int,Int))]
tex_tokens = do 
    b <- is_eof
    if b
        then return []
        else do
            c <- match_first [
                    (is_space, Blank),
                    (is_command, Command),
                    (match_string "{", (\_ -> Open True)),
                    (match_string "}", (\_ -> Close True)),
                    (match_string "[", (\_ -> Open False)),
                    (match_string "]", (\_ -> Close False)) ]
            case c of
                Just x  -> do
                    (i,j) <- line_info
                    xs <- tex_tokens
                    return ((x,(i,j)):xs)
                Nothing -> do
                    (i,j) <- line_info
                    d <- read_char
                    xs <- tex_tokens
                    case xs of
                        (TextBlock ys,_):zs -> 
                            return ((TextBlock (d:ys),(i,j)):zs)
                        _ ->return ((TextBlock [d],(i,j)):xs)
                
        
read_lines :: Scanner Char a -> String -> Either (String, Int, Int) a 
read_lines s xs = read_tokens s (line_number xs)

read_tokens :: Scanner a b -> [(a, (Int,Int))] -> Either (String, Int, Int) b
read_tokens (Scanner f) xs = 
        do  (r, State xs i j) <- f (State xs 0 0)
            case xs of 
                [] -> return r
                _ -> Left ("expected end of file", i, j)
        

choice :: [Scanner a b] -> Scanner a b
choice [] = fail "no valid choice"
choice (Scanner f:xs) = Scanner g
    where
        g s0 = case f s0 of
                    Left  _ -> 
                        case choice xs of
                            Scanner h -> h s0
                    x -> x

latex_content :: Scanner LatexToken [LatexDoc]
latex_content = do
    b <- is_eof
    if b
    then return []
    else do
        c:_ <- peek
        case c of
            Command "\\begin" -> do
                    begin_block
            Open c0 -> do
                    read_char
                    ct <- latex_content
                    c <- read_char
                    case c of
                        Close c1 -> do
                            unless (c0 == c1) $ fail "mismatched brackets"
                        _ -> fail "expected closing bracket"
                    rest <- latex_content 
                    return (Bracket c0 ct:rest)
            Close _ ->         return []
            Command "\\end" -> return []
            t@(Blank s)     -> content_token t
            t@(TextBlock s) -> content_token t
            t@(Command s)   -> content_token t

content_token t = do
        read_char
        xs <- latex_content
        case xs of
            Text y:ys -> 
                return (Text (t:y):ys)
            _ -> 
                return (Text [t]:xs)

opt_args :: Scanner LatexToken [[LatexDoc]]
opt_args = return []

skip_blank = do
        xs <- peek
        case xs of
            (Blank _:xs) -> do read_char ; return ()
            _  -> return ()

argument :: Scanner LatexToken [LatexDoc]
argument = do
        skip_blank
        xs <- peek
        case xs of
            Open True:_ -> do  
                read_char
                ct <- latex_content
                Close True <- read_char
                return ct
            _ -> fail "expecting brackets '{'"            

begin_block :: Scanner LatexToken [LatexDoc]
begin_block = do
    read_char
    oargs <- opt_args
    args0 <- argument
    ct    <- latex_content
    end   <- read_char
    unless (end == Command "\\end") $ 
        fail ("expected \\end{" ++ concatMap source args0 ++ "}, read \'" ++ lexeme end ++ "\'")
    args1 <- argument
    unless (args0 == args1) $ fail "begin / end do not match"
    case args0 of
        [Text [TextBlock s]] -> do
            rest <- latex_content 
            return (Env s oargs ct:rest)
        _  -> fail "name of a begin / end block must be a simple string"    

latex_structure :: String -> Either (String, Int, Int) [LatexDoc]
latex_structure xs = do
        ys <- read_lines tex_tokens (uncomment xs)
        read_tokens latex_content ys

--tokens ('\\':xs)    
--        | isAlpha $ head xs = 
--            Command ('\\' : [head xs] ++ takeWhile isAlphaNum (tail xs))
--            : tokens (dropWhile isAlphaNum (tail xs))
--        | otherwise = 
--            Command ('\\' : [head xs]) : tokens (tail xs)
--tokens (x:xs)       = 
--        case tokens xs of
--            Command xs:ys   -> TextBlock [x] : Command xs : ys
--            TextBlock xs:ys -> TextBlock (x:xs) : ys
--tokens []           = []

is_prefix xs ys = xs == take (length xs) ys

--latex_doc 

--latex_doc = do xs <- many latex_element ; eos ; return xs
--
--latex_element :: ReadP LatexDoc
--latex_element = block <++ text_block
--
--block = do
--    b <- string begin_kw
--    kw1 <- bracket
--    t <- latex_doc
--    e <- string end_kw
--    kw2 <- bracket
--    return (Env kw1 t kw2)
--
--bracket = do
--    skipSpaces
--    char '{'
--    xs <- munch (\x -> x /= '{' && x /= '}')
--    char '}'
--    return xs
--
--eos = do(eof <++ 
--          (do   xs <- look ; 
--                guard (is_prefix end_kw xs))) ; 
--        return []
--
--text_block = do
--    xs <- text
--    return $ Text xs
--
--text = (do
--            ys <- look
--            guard (not $ is_prefix end_kw ys)
--            guard (not $ is_prefix begin_kw ys)
--            c <- get 
--            xs <- text
--            return (c:xs))
--    <++ (return [])

uncomment xs = unlines $ map (takeWhile ('%' /=)) $ lines xs

--latex_content xs = fst $ head $ readP_to_S latex_doc $ uncomment xs

--test = do
--        let path = "/Users/simonhudon/Documents/ecole"
--                ++ "/YorkU/SEL/research/tools-methods/PAT"
--                ++ "/Devel/Docs/paper/sections/pacemaker.tex"
----        let path = "/Users/simonhudon/Documents/ecole"
----                ++ "/YorkU/SEL/research/tools-methods/PAT"
----                ++ "/Devel/Docs/paper/TTM.tex"
--        ct <- readFile path
--        let uc = uncomment ct
--        let res = fst $ head (readP_to_S latex_doc uc)
----        return res
--        return $ find ["tabular"] res

find :: [String] -> [LatexDoc] -> Map String [LatexDoc]
find kw (e@(Env b _ c):xs)
    | b `elem` kw     = insertWith (++) b [e] $ find kw xs
    | otherwise       = unionWith (++) (find kw c) (find kw xs)
find kw (Bracket _ c:xs) = unionWith (++) (find kw c) (find kw xs)
find kw (_:xs)        = find kw xs
find _  []            = empty


--parse_latex :: String -> ([LatexDoc], String)
--parse_latex (x:xs)
--    | is_prefix (x:xs) begin_kw = 
--        case parse_latex (drop (length begin_kw) (x:xs)) of
--            (ws, ys) -> 
--                case parse_latex $ drop (length end_kw) ys of
--                    (vs,us) -> (Env begin_kw ws end_kw:vs, us)
--    | is_prefix (x:xs) end_kw   = ([], (x:xs))
--    | otherwise                 = 
--        case parse_latex xs of
--            (Text zs:ws, ys)   -> (Text (x:zs):ws, ys)
--            (ws, ys)           -> (Text [x]:ws, ys) 
--parse_latex [] = ([], [])
