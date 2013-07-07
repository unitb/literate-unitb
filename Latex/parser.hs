module Latex.Parser where
    -- TODO: Separate Latex from the Scanner monad


import Control.Monad

import Data.Char
import Data.Map hiding ( map, null )

import Latex.Scanner

import System.IO.Unsafe

data LatexDoc = 
        Env String (Int,Int) [LatexDoc] (Int,Int)
        | Bracket Bool (Int,Int) [LatexDoc] (Int,Int)
        | Text [Cell LatexToken]
    deriving (Eq)

flatten (Env s _ ct _) = 
           "\\begin{" ++ s ++ "}"
        ++ concatMap flatten ct
        ++ "\\end{" ++ s ++ "}"
flatten (Bracket b _ ct _) = b0 ++ concatMap flatten ct ++ b1
    where
        (b0,b1) = if b
            then ("{", "}")
            else ("[", "]")
flatten (Text xs) = concatMap (lexeme . item) xs

flatten_li (Env s (i0,j0) ct (i1,j1)) = 
           zip ("\\begin{" ++ s ++ "}") (zip (repeat i0) [j0..])
        ++ concatMap flatten_li ct
        ++ zip ("\\end{" ++ s ++ "}") (zip (repeat i1) [j1..])
flatten_li (Text xs)        = concatMap lexeme_li xs
flatten_li (Bracket b (i0,j0) ct (i1,j1)) 
        = (b0,(i0,j0)) : concatMap flatten_li ct ++ [(b1,(i1,j1))]
    where
        (b0,b1) = if b
            then ('{', '}')
            else ('[', ']')

data Cell a = Cell { item :: a, line :: Int, col :: Int }
    deriving Eq

instance Show a => Show (Cell a) where
    show x = show $ item x

data LatexToken =
        Command String
        | TextBlock String
        | Blank String
        | Open Bool | Close Bool
    deriving (Eq, Show)

instance Show LatexDoc where
    show (Env b _ xs _) = "Env{" ++ b ++ "} (" ++ show (length xs) ++ ")"
    show (Text xs)      = "Text (" ++ show (take 10 xs) ++ "...)"
    show (Bracket True _ c _)  = "Bracket {" ++ show c ++ "} "
    show (Bracket False _ c _) = "Bracket [" ++ show c ++ "] "

--instance Show LatexDoc where
--    show (Env b li0 xs _) = "Env" ++ show li0 ++ "{" ++ b ++ "} (" ++ show (length xs) ++ ")"
--    show (Text xs)      = "Text (" ++ show (map lexeme_li (take 10 xs)) ++ "...)"
--    show (Bracket True li c _)  = "Bracket" ++ show li ++ " {" ++ show c ++ "} "
--    show (Bracket False li c _) = "Bracket" ++ show li ++ " [" ++ show c ++ "] "


source (Text xs) = concatMap (lexeme . item) xs
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

lexeme_li (Cell x i j) = zip (lexeme x) $ zip (repeat i) [j ..]

begin_kw = "\\begin"
end_kw   = "\\end"

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

tex_tokens :: Scanner Char [(LatexToken,(Int,Int))]
tex_tokens = do 
    b <- is_eof
    if b
        then return []
        else do
            c <- match_first [
                    (is_space, \xs -> return $ Just $ Blank xs),
                    (is_command, \xs -> return $ Just $ Command xs),
                    (match_string "{", (\_ -> return (Just $ Open True))),
                    (match_string "}", (\_ -> return (Just $ Close True))),
                    (match_string "[", (\_ -> return (Just $ Open False))),
                    (match_string "]", (\_ -> return (Just $ Close False))) ]
                    (return Nothing)
            case c of
                Just x  -> do
                    li <- line_info
                    xs <- tex_tokens
                    return ((x,li):xs)
                Nothing -> do
                    li <- line_info
                    d  <- read_char
                    xs <- tex_tokens
                    case xs of
                        (TextBlock ys,_):zs -> 
                            return ((TextBlock (d:ys),li):zs)
                        _ ->return ((TextBlock [d],li):xs)

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
                    (i0,j0) <- line_info
                    ct <- latex_content
                    c  <- read_char
                    (i1,j1) <- line_info
                    case c of
                        Close c1 -> do
                            unless (c0 == c1) $ fail "mismatched brackets"
                        _ -> fail "expected closing bracket"
                    rest <- latex_content 
                    return (Bracket c0 (i0,j0) ct (i1,j1):rest)
            Close _ ->         return []
            Command "\\end" -> return []
            t@(Blank s)     -> content_token t
            t@(TextBlock s) -> content_token t
            t@(Command s)   -> content_token t

content_token :: LatexToken -> Scanner LatexToken [LatexDoc]
content_token t = do
        read_char
        (i,j) <- line_info
        xs <- latex_content
        case xs of
            Text y:ys -> 
                return (Text ((Cell t i j):y):ys)
            _ -> 
                return (Text [(Cell t i j)]:xs)

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
    li0 <- line_info
--    oargs <- opt_args
    args0 <- argument
    ct    <- latex_content
    end   <- read_char
    li1   <- line_info
    unless (end == Command "\\end") $ 
        fail ("expected \\end{" ++ concatMap source args0 ++ "}, read \'" ++ lexeme end ++ "\'")
    args1 <- argument
    (begin, end) <- 
        case (args0, args1) of
            ( [Text [Cell (TextBlock begin) _ _]],
              [Text [Cell (TextBlock end) _ _]] ) -> do
                return (begin, end)
            _  -> fail "name of a begin / end block must be a simple string"    
    unless (begin == end) $ 
        fail ("begin / end do not match: " ++ begin ++ " / " ++ end)
    rest <- latex_content 
    return (Env begin li0 ct li1:rest)

latex_structure :: String -> Either (String, Int, Int) [LatexDoc]
latex_structure xs = do
        ys <- read_lines tex_tokens (uncomment xs)
        read_tokens latex_content ys

is_prefix xs ys = xs == take (length xs) ys

uncomment :: String -> String
uncomment xs = unlines $ map (takeWhile ('%' /=)) $ lines xs

with_print x = unsafePerformIO (do putStrLn $ show x ; return x)

find_env :: [String] -> [LatexDoc] -> Map String [LatexDoc]
find_env kw (e@(Env b _ c _):xs)
    | b `elem` kw     = insertWith (++) b [e] $ find_env kw xs
    | otherwise       = unionWith (++) (find_env kw c) (find_env kw xs)
find_env kw (Bracket _ _ c _:xs) = unionWith (++) (find_env kw c) (find_env kw xs)
find_env kw (_:xs)        = find_env kw xs
find_env kw []            = fromList $ map (\x -> (x, [])) kw 

find_cmd :: [String] -> [LatexDoc] -> Map String [[LatexDoc]]
find_cmd kw (Env b _ c _:xs)         = unionWith (++) (find_cmd kw c) $ find_cmd kw xs
find_cmd kw (Bracket _ _ c _:xs)       = unionWith (++) (find_cmd kw c) $ find_cmd kw xs
find_cmd kw e@((Text (Cell (Command c) _ _:ys):xs))
    | c `elem` kw                  = insertWith (++) c [e :: [LatexDoc]] $
                                        find_cmd kw (Text ys:xs)
    | otherwise                    = find_cmd kw (Text ys:xs)
find_cmd kw (Text (_:ys):xs)       = find_cmd kw (Text ys:xs)
find_cmd kw (Text []:xs)           = find_cmd kw xs
find_cmd kw []                     = fromList $ map (\x -> (x,[])) kw

