module Latex.Parser where

    -- Modules
import Latex.Scanner

    -- Libraries
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import Data.Char
import Data.Either
import Data.Function
import Data.Graph
import Data.List ( intercalate )
import Data.Map as M hiding ( foldl, map, null, (!) )

import System.Directory
import System.IO.Unsafe
import System.FilePath

import Utilities.Format
import Utilities.Graph
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

fold_doc f x (Env _ _ c _)     = foldl f x c
fold_doc f x (Bracket _ _ c _) = foldl f x c
fold_doc _ x (Text _)          = x

fold_docM f x (Env _ _ c _)     = foldM f x c
fold_docM f x (Bracket _ _ c _) = foldM f x c
fold_docM _ x (Text _)          = return x

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
    | b                 = "{"
    | otherwise         = "["
lexeme (Close b _)
    | b                 = "}"
    | otherwise         = "]"

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
            t@(Blank _ _)     -> content_token t
            t@(TextBlock _ _) -> content_token t
            t@(Command _ _)   -> content_token t

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
            (Blank _ _:_) -> do read_char ; return ()
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

type DocWithHoles = Either (String,(Int,Int)) (LatexToken,(Int,Int))

find_input_cmd :: Scanner LatexToken [DocWithHoles]
find_input_cmd = do
        b <- is_eof
        if b then return []
        else do
            r <- read_char 
            case r of
                Command "\\input" li -> do
                    ts <- peek
                    fn <- case ts of
                        Blank _ _ 
                            : Open True _ 
                            : TextBlock fn _
                            : Close True _
                            : _ -> do
                                forM_ [1..4]  $ const $ read_char
                                return fn
                        Open True _ 
                            : TextBlock fn _
                            : Close True _
                            : _ -> do
                                forM_ [1..3] $ const $ read_char
                                return fn
                        _ -> fail "invalid syntax for \\input command"
                    rs <- find_input_cmd
                    return $ Left (fn,li) : rs
                _ -> do
                    rs <- find_input_cmd
                    return $ Right (r,line_info r) : rs

scan_file :: String -> Either [Error] [DocWithHoles]
scan_file xs = do
        ys <- read_lines tex_tokens (uncomment xs)
        read_tokens find_input_cmd ys (1,1)
        
--        read_tokens latex_content ys (1,1)

do_while cmd = do
        b <- cmd
        if b then
            do_while cmd
        else return ()

fill_holes :: String -> Map String [DocWithHoles] -> Either [Error] [(LatexToken,(Int,Int))]
fill_holes fname m = do
        (_,m) <- foldM propagate (m,empty) order
        return (m ! fname)
    where
        propagate (m0,m1) (AcyclicSCC v) = Right (m0, insert v (g (m0 ! v) m1) m1)
        propagate _ (CyclicSCC xs) = Left  [(format msg $ intercalate "," xs,0,0)]
        g :: [DocWithHoles]
          -> Map String [(LatexToken,(Int,Int))] 
          -> [(LatexToken,(Int,Int))]
        g doc m = concatMap (h m) doc
        h :: Map String [(LatexToken,(Int,Int))] 
          -> DocWithHoles
          -> [(LatexToken,(Int,Int))] 
        h _ (Right x)       = [x]
        h m (Left (name,_)) = m ! name
        msg = "A cycle exists in the LaTeX document structure: {0}"
        order = cycles_with [fname] edges 
        edges :: [(String,String)]
        edges    = concatMap f $ toList m
        f (x,ys) = [ (x,y) | y <- map fst $ lefts ys ]
        m ! x = case M.lookup x m of
                    Just y  -> y
                    Nothing -> error $ 
                        "Map.!: given key is not an element in the map: " 
                        ++ show x ++ " - " ++ show (keys m) ++ " - " ++ show order

scan_doc :: String -> IO (Either [Error] [(LatexToken,(Int,Int))])
scan_doc fname = runEitherT $ do
    let dir = takeDirectory fname
    cd <- liftIO $ getCurrentDirectory
    fname <- liftIO $ canonicalizePath fname
--    liftIO $ putStrLn cd
    (m,xs) <- flip execStateT (empty,[(fname,(1,1))]) 
--            $ do_while
            $ fix $ \rec -> do
        (m,ys) <- get
--        liftIO $ putStrLn $ "ys = " ++ show ys
        case ys of
            (x,(i,j)):xs -> do
--                liftIO $ putStrLn x
--                liftIO $ putStrLn $ show xs
                b0 <- liftIO $ doesFileExist $ x
                b1 <- liftIO $ doesFileExist $ (x ++ ".tex")
                x <- if b1 
                    then return $ (x ++ ".tex")
                    else return $ x
                if not b0 && not b1 then
                    lift $ left [("file " ++ x ++ " does not exist",i,j)]
                else if not $ x `member` m then do
                    ct  <- liftIO $ readFile x
                    ct  <- lift $ hoistEither $ scan_file ct
                    ct  <- forM ct $ \path -> do
                        either 
                            (\(path,(i,j)) -> do
                                b0 <- liftIO $ doesFileExist $ dir </> path
                                b1 <- liftIO $ doesFileExist $ (dir </> path ++ ".tex")
                                path <- if b1 
                                    then return $ (dir </> path ++ ".tex")
                                    else return $ dir </> path
                                if b0 || b1 then do
                                    path <- liftIO $ canonicalizePath path
                                    return $ Left (path,(i,j))
                                else return $ Left (path,(i,j)))
                            (return . Right) path
--                    liftIO $ putStrLn $ show (lefts ct) -- $ putStrLn . show 
                    put (insert x ct m,xs ++ lefts ct)
                else put (m,xs)
                rec
            [] -> return ()
    unless (null xs) $ error "scan_doc: xs should be null"
    hoistEither $ fill_holes fname m
        

parse_latex_document :: String -> IO (Either [Error] [LatexDoc])
parse_latex_document fname = runEitherT $ do
        ys <- EitherT $ scan_doc fname 
        hoistEither $ read_tokens latex_content ys (1,1)

latex_structure :: String -> Either [Error] [LatexDoc]
latex_structure xs = do
        ys <- read_lines tex_tokens (uncomment xs)
        read_tokens latex_content ys (1,1)

is_prefix xs ys = xs == take (length xs) ys

uncomment :: String -> String
uncomment xs = unlines $ map (takeWhile ('%' /=)) $ lines xs

with_print x = unsafePerformIO (do putStrLn $ show x ; return x)
