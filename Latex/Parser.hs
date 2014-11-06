module Latex.Parser where

    -- Modules
import Latex.Scanner

    -- Libraries
import Control.Monad
-- import Control.Monad.IO.Class
import Control.Monad.Trans -- .Class
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
import Utilities.Graph hiding ( map, empty )
import Utilities.Syntactic

data LatexDoc = 
        Env String LineInfo [LatexDoc] LineInfo
        | Bracket Bool LineInfo [LatexDoc] LineInfo
        | Text [LatexToken]
    deriving (Eq)

flatten :: LatexDoc -> [Char]
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

whole_line :: LineInfo -> [LineInfo]
whole_line (LI fn i j) = map (uncurry3 LI) $ zip3 (repeat fn) (repeat i) [j..]

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x,y,z) = f x y z

flatten_li :: LatexDoc -> [(Char,LineInfo)]
flatten_li (Env s li1 ct li0) = 
           zip ("\\begin{" ++ s ++ "}") (whole_line li0)
        ++ concatMap flatten_li ct
        ++ zip ("\\end{" ++ s ++ "}") (whole_line li1)
flatten_li (Text xs)        = concatMap lexeme_li xs
flatten_li (Bracket b li0 ct li1) 
        = (b0,li0) : concatMap flatten_li ct ++ [(b1,li1)]
    where
        (b0,b1) = if b
            then ('{', '}')
            else ('[', ']')

fold_doc :: (a -> LatexDoc -> a)
         -> a -> LatexDoc -> a
fold_doc f x doc  = foldl f x $ contents doc

fold_docM :: Monad m
          => (a -> LatexDoc -> m a)
          -> a -> LatexDoc -> m a
fold_docM f x doc = foldM f x $ contents doc

map_doc :: (LatexDoc -> b)
        -> LatexDoc -> [b]
map_doc f doc = map f $ contents doc

map_docM :: Monad m 
         => (LatexDoc -> m b)
         -> LatexDoc -> m [b]
map_docM f doc = mapM f $ contents doc

contents :: LatexDoc -> [LatexDoc]
contents (Env _ _ c _)     = c
contents (Bracket _ _ c _) = c
contents (Text _)          = []

data LatexToken =
        Command String LineInfo
        | TextBlock String LineInfo
        | Blank String LineInfo
        | Open Bool LineInfo
        | Close Bool LineInfo
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

source :: LatexDoc -> String
source (Text xs) = concatMap lexeme xs
source x         = show x

lexeme :: LatexToken -> String
lexeme (Command xs _)   = xs
lexeme (TextBlock xs _) = xs
lexeme (Blank xs _)     = xs
lexeme (Open b _)
    | b                 = "{"
    | otherwise         = "["
lexeme (Close b _)
    | b                 = "}"
    | otherwise         = "]"

lexeme_li :: LatexToken -> [(Char, LineInfo)]
lexeme_li x = zip (lexeme x) $ whole_line li
    where
        li    = line_info x

begin_kw :: String
end_kw   :: String

begin_kw = "\\begin"
end_kw   = "\\end"

is_identifier :: String -> Maybe Int
is_identifier []    = Nothing
is_identifier (x:xs)
    | isAlpha x     = Just (1 + length (takeWhile isAlphaNum xs))
    | otherwise     = Nothing 

is_command :: String -> Maybe Int
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

tex_tokens :: Scanner Char [(LatexToken,LineInfo)]
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
            li <- get_line_info
            case c of
                Just x  -> do
                    xs <- tex_tokens
                    return ((x,li):xs)
                Nothing -> do
                    d  <- read_char
                    li <- get_line_info
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
                    li0 <- get_line_info
                    ct  <- latex_content
                    c   <- read_char
                    li1 <- get_line_info
                    case c of
                        Close c1 _ -> do
                            unless (c0 == c1) $ fail "mismatched brackets"
                        _ -> fail "expected closing bracket"
                    rest <- latex_content 
                    return (Bracket c0 li0 ct li1:rest)
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

skip_blank :: Scanner LatexToken ()
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
--    let li0 = LI fn0 i0 j0 
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

type DocWithHoles = Either (String,LineInfo) (LatexToken,LineInfo)

find_input_cmd :: Scanner LatexToken [DocWithHoles]
find_input_cmd = do
        b <- is_eof
        if b then return []
        else do
            r  <- read_char 
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

scan_file :: FilePath -> String 
          -> Either [Error] [DocWithHoles]
scan_file fname xs = do
        ys <- read_lines tex_tokens fname (uncomment xs)
        read_tokens find_input_cmd fname ys (1,1)
        
--        read_tokens latex_content ys (1,1)

do_while :: Monad m
         => m Bool -> m ()
do_while cmd = do
        b <- cmd
        if b then
            do_while cmd
        else return ()

fill_holes :: String -> Map String [DocWithHoles] -> Either [Error] [(LatexToken,LineInfo)]
fill_holes fname m = do
        (_,m) <- foldM propagate (m,empty) order
        return (m ! fname)
    where
        propagate (m0,m1) (AcyclicSCC v) = Right (m0, insert v (g (m0 ! v) m1) m1)
        propagate _ (CyclicSCC xs@(y:_)) = Left 
            [ (Error (format msg $ intercalate "," xs) 
                $ LI y 1 1)]
        propagate _ (CyclicSCC []) = error "fill_holes: a cycle has to include two or more vertices"
        g :: [DocWithHoles]
          -> Map String [(LatexToken,LineInfo)] 
          -> [(LatexToken,LineInfo)] 
        g doc m = concatMap (h m) doc
        h :: Map String [(LatexToken,LineInfo)] 
          -> DocWithHoles
          -> [(LatexToken,LineInfo)] 
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

scan_doc :: String -> IO (Either [Error] [(LatexToken,LineInfo)])
scan_doc fname = runEitherT $ do
    let dir = takeDirectory fname
    fname  <- liftIO $ canonicalizePath fname
    (m,xs) <- flip execStateT (empty,[(fname,(LI fname 1 1))]) 
            $ fix $ \rec -> do
        (m,ys) <- get
        case ys of
            (x,(LI _ i j)):xs -> do
                if not $ x `member` m then do
                    ct  <- liftIO $ readFile x
                    ct  <- lift $ hoistEither $ scan_file x ct
                    ct  <- forM ct $ \path -> do
                        either 
                            (\(path,li) -> do
                                b0 <- liftIO $ doesFileExist $ dir </> path
                                b1 <- liftIO $ doesFileExist $ (dir </> path ++ ".tex")
                                path <- if b1 
                                    then return $ (dir </> path ++ ".tex")
                                    else if b0 
                                    then return $ dir </> path
                                    else lift $ left 
                                        [ Error ("file '" ++ path ++ "' does not exist") 
                                            $ LI x i j]
                                path <- liftIO $ canonicalizePath path
                                return $ Left (path,li))
                            (return . Right) path
                    put (insert x ct m,xs ++ lefts ct)
                else put (m,xs)
                rec
            [] -> return ()
    unless (null xs) $ error "scan_doc: xs should be null"
    hoistEither $ fill_holes fname m
        

parse_latex_document :: String -> IO (Either [Error] [LatexDoc])
parse_latex_document fname = runEitherT $ do
        ys <- EitherT $ scan_doc fname 
        hoistEither $ read_tokens latex_content fname ys (1,1)

latex_structure :: FilePath -> String -> Either [Error] [LatexDoc]
latex_structure fn xs = do
        ys <- read_lines tex_tokens fn (uncomment xs)
        read_tokens latex_content fn ys (1,1)

is_prefix :: Eq a => [a] -> [a] -> Bool
is_prefix xs ys = xs == take (length xs) ys

uncomment :: String -> String
uncomment xs = unlines $ map (takeWhile ('%' /=)) $ lines xs

with_print :: Show a => a -> a
with_print x = unsafePerformIO (do putStrLn $ show x ; return x)
