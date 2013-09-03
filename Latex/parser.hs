module Latex.Parser where

    -- Modules
import Latex.Scanner

    -- Libraries
import Control.Monad

import Data.Char
import Data.Map hiding ( foldl, map, null )

import System.IO.Unsafe

import Utilities.Format
import Utilities.Syntactic

data LatexDoc = 
        Env String (Int,Int) [LatexDoc] (Int,Int)
        | Bracket Bool (Int,Int) [LatexDoc] (Int,Int)
        | Text [LatexToken]
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
flatten (Text xs) = concatMap lexeme xs

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

fold_doc f x (Env s _ c _)     = foldl f x c
fold_doc f x (Bracket _ _ c _) = foldl f x c
fold_doc f x (Text _)          = x

fold_docM f x (Env s _ c _)     = foldM f x c
fold_docM f x (Bracket _ _ c _) = foldM f x c
fold_docM f x (Text _)          = return x

data LatexToken =
        Command String (Int, Int)
        | TextBlock String (Int, Int)
        | Blank String (Int, Int)
        | Open Bool (Int, Int) 
        | Close Bool (Int, Int)
    deriving (Eq, Show)

instance Show LatexDoc where
    show (Env b _ xs _) = "Env{" ++ b ++ "} (" ++ show (length xs) ++ ")"
    show (Text xs)      = "Text (" ++ show (take 10 xs) ++ "...)"
    show (Bracket True _ c _)  = "Bracket {" ++ show c ++ "} "
    show (Bracket False _ c _) = "Bracket [" ++ show c ++ "] "

instance Syntactic LatexToken where
    line_info (Command _ li)    = li
    line_info (TextBlock _ li)  = li
    line_info (Blank _ li)      = li
    line_info (Open _ li)       = li
    line_info (Close _ li)      = li

instance Syntactic LatexDoc where
    line_info (Env _ li _ _)     = li
    line_info (Bracket _ li _ _) = li
    line_info (Text xs)          = line_info $ head xs

instance Syntactic a => Syntactic [a] where
    line_info xs = line_info $ head xs

source (Text xs) = concatMap lexeme xs
source x         = show x

lexeme (Command xs _)   = xs
lexeme (TextBlock xs _) = xs
lexeme (Blank xs _)     = xs
lexeme (Open b _)
    | b               = "{"
    | not b           = "["
lexeme (Close b _)
    | b               = "}"
    | not b           = "]"

lexeme_li x = zip (lexeme x) $ zip (repeat i) [j ..]
    where
        (i,j) = line_info x

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
            li <- get_line_info
            c <- match_first [
                    (is_space, \xs -> return $ Just $ Blank xs li),
                    (is_command, \xs -> return $ Just $ Command xs li),
                    (match_string "{", (\_ -> return (Just $ Open True li))),
                    (match_string "}", (\_ -> return (Just $ Close True li))),
                    (match_string "[", (\_ -> return (Just $ Open False li))),
                    (match_string "]", (\_ -> return (Just $ Close False li))) ]
                    (return Nothing)
            case c of
                Just x  -> do
                    xs <- tex_tokens
                    return ((x,li):xs)
                Nothing -> do
                    d  <- read_char
                    xs <- tex_tokens
                    case xs of
                        (TextBlock ys _,_):zs -> 
                            return ((TextBlock (d:ys) li,li):zs)
                        _ ->return ((TextBlock [d] li,li):xs)

latex_content :: Scanner LatexToken [LatexDoc]
latex_content = do
    b <- is_eof
    if b
    then return []
    else do
        c:_ <- peek
        case c of
            Command "\\begin" _ -> do
                    begin_block
            Open c0 _ -> do
                    read_char
                    (i0,j0) <- get_line_info
                    ct <- latex_content
                    c  <- read_char
                    (i1,j1) <- get_line_info
                    case c of
                        Close c1 _ -> do
                            unless (c0 == c1) $ fail "mismatched brackets"
                        _ -> fail "expected closing bracket"
                    rest <- latex_content 
                    return (Bracket c0 (i0,j0) ct (i1,j1):rest)
            Close _ _ ->         return []
            Command "\\end" _ -> return []
            t@(Blank s _)     -> content_token t
            t@(TextBlock s _) -> content_token t
            t@(Command s _)   -> content_token t

content_token :: LatexToken -> Scanner LatexToken [LatexDoc]
content_token t = do
        read_char
        xs    <- latex_content
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
            (Blank _ _:xs) -> do read_char ; return ()
            _  -> return ()

argument :: Scanner LatexToken [LatexDoc]
argument = do
        skip_blank
        xs <- peek
        case xs of
            Open True _:_ -> do  
                read_char
                ct <- latex_content
                close <- read_char
                case close of
                    Close True _ -> return ct
                    _ -> fail "expecting closing bracket '}'"        
            _ -> fail "expecting opening bracket '{'"            

begin_block :: Scanner LatexToken [LatexDoc]
begin_block = do
    read_char
    li0 <- get_line_info
    args0 <- argument
    ct    <- latex_content
    end   <- read_char
    li1   <- get_line_info
    unless (end == Command "\\end" (line_info end)) $ 
        fail ("expected \\end{" ++ concatMap source args0 ++ "}, read \'" ++ lexeme end ++ "\'")
    args1 <- argument
    (begin, li2, end, li3) <- 
        case (args0, args1) of
            ( [Text [TextBlock begin li0]],
              [Text [TextBlock end li1]] ) -> do
                return (begin, li0, end, li1)
            _  -> fail "name of a begin / end block must be a simple string"    
    unless (begin == end) $ 
        fail (format "begin / end do not match: {0} {1} / {2} {3}" begin li2 end li3)
    rest <- latex_content 
    return (Env begin li0 ct li1:rest)

latex_structure :: String -> Either [Error] [LatexDoc]
latex_structure xs = do
        ys <- read_lines tex_tokens (uncomment xs)
        read_tokens latex_content ys (1,1)

is_prefix xs ys = xs == take (length xs) ys

uncomment :: String -> String
uncomment xs = unlines $ map (takeWhile ('%' /=)) $ lines xs

with_print x = unsafePerformIO (do putStrLn $ show x ; return x)
