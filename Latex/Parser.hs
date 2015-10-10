module Latex.Parser where

    -- Modules
import Latex.Scanner 

    -- Libraries
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans -- .Class
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import Data.Char
import Data.Either
import Data.Function
import Data.Graph
import Data.List ( intercalate )
import Data.Map as M hiding ( foldl, map, null, (!) )
import Data.Semigroup

import Safe

import System.Directory
import System.IO.Unsafe
import System.FilePath

import Utilities.Format
import Utilities.Graph hiding ( map, empty )
import Utilities.Syntactic

data LatexNode = 
        Env String LineInfo LatexDoc LineInfo
        | Bracket BracketType LineInfo LatexDoc LineInfo
        | Text [LatexToken] LineInfo
    deriving (Eq)

data LatexDoc = Doc [LatexNode] LineInfo
    deriving (Eq)

data BracketType = Curly | Square
    deriving (Eq,Show)

instance Semigroup LatexDoc where
    (<>) (Doc xs _) (Doc ys li) = Doc (xs++ys) li

class Convertible a where
    flatten :: a -> String

flatten' :: LatexDoc -> String
flatten' (Doc xs _) = concatMap flatten xs

instance Convertible LatexDoc where
    flatten = flatten'

instance Convertible LatexNode where
    flatten (Env s _ ct _) = 
               "\\begin{" ++ s ++ "}"
            ++ flatten' ct
            ++ "\\end{" ++ s ++ "}"
    flatten (Bracket b _ ct _) = b0 ++ flatten' ct ++ b1
        where
            (b0,b1) = case b of
                Curly -> ("{", "}")
                Square -> ("[", "]")
    flatten (Text xs _) = concatMap lexeme xs

instance Convertible StringLi where
    flatten (StringLi xs _) = map fst xs

whole_line :: LineInfo -> [LineInfo]
whole_line (LI fn i j) = map (uncurry3 LI) $ zip3 (repeat fn) (repeat i) [j..]

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x,y,z) = f x y z

flatten_li' :: LatexDoc -> StringLi
flatten_li' (Doc xs li) = StringLi (concatMap flatten_li xs) li

getString :: StringLi -> [(Char,LineInfo)]
getString (StringLi xs _) = xs

flatten_li :: LatexNode -> [(Char,LineInfo)]
flatten_li (Env s li1 ct li0) = 
           zip ("\\begin{" ++ s ++ "}") (whole_line li0)
        ++ getString (flatten_li' ct)
        ++ zip ("\\end{" ++ s ++ "}") (whole_line li1)
flatten_li (Text xs _)        = concatMap lexeme_li xs
flatten_li (Bracket b li0 ct li1) 
        = (b0,li0) : getString (flatten_li' ct) ++ [(b1,li1)]
    where
        (b0,b1) = case b of
            Curly -> ('{', '}')
            Square -> ('[', ']')

fold_doc :: (a -> LatexNode -> a)
         -> a -> LatexNode -> a
fold_doc f x doc  = foldl f x $ contents' $ contents doc

fold_docM :: Monad m
          => (a -> LatexNode -> m a)
          -> a -> LatexNode -> m a
fold_docM f x doc = foldM f x $ contents' $ contents doc

map_doc :: (LatexNode -> b)
        -> LatexNode -> [b]
map_doc f doc = map f $ contents' $ contents doc

map_docM :: Monad m 
         => (LatexNode -> m b)
         -> LatexNode -> m [b]
map_docM f doc = mapM f $ contents' $ contents doc

map_docM_ :: Monad m 
         => (LatexNode -> m b)
         -> LatexNode -> m ()
map_docM_ f doc = mapM_ f $ contents' $ contents doc

contents :: LatexNode -> LatexDoc
contents (Env _ _ c _)     = c
contents (Bracket _ _ c _) = c
contents (Text _ li)          = Doc [] li

contents' :: LatexDoc -> [LatexNode]
contents' (Doc xs _) = xs

unconsTex :: LatexDoc -> Maybe (LatexNode,LatexDoc)
unconsTex (Doc (x:xs) li) = Just (x,Doc xs li)
unconsTex (Doc [] _)      = Nothing

consTex :: LatexNode -> LatexDoc -> LatexDoc
consTex x (Doc xs li) = Doc (x:xs) li

data LatexToken =
        Command String LineInfo
        | TextBlock String LineInfo
        | Blank String LineInfo
        | Open BracketType LineInfo
        | Close BracketType LineInfo
    deriving (Eq, Show)

instance Show LatexNode where
    show (Env b _ xs _) = "Env{" ++ b ++ "} (" ++ show (length $ contents' xs) ++ ")"
    show (Text xs _)    = "Text (" ++ show (take 10 xs) ++ "...)"
    show (Bracket Curly _ c _)  = "Bracket {" ++ show c ++ "} "
    show (Bracket Square _ c _) = "Bracket [" ++ show c ++ "] "

instance Show LatexDoc where
    show (Doc xs _) = show xs

instance Syntactic LatexToken where
    line_info (Command _ li)    = li
    line_info (TextBlock _ li)  = li
    line_info (Blank _ li)      = li
    line_info (Open _ li)       = li
    line_info (Close _ li)      = li

instance Syntactic LatexNode where
    line_info (Env _ li _ _)     = li
    line_info (Bracket _ li _ _) = li
    line_info (Text xs li)          = headDef li $ map line_info xs

instance Syntactic StringLi where
    line_info (StringLi xs li) = headDef li (map snd xs)

instance Syntactic LatexDoc where
    line_info (Doc xs li) = headDef li (map line_info xs)


source :: LatexNode -> String
source (Text xs _) = concatMap lexeme xs
source x           = show x

lexeme :: LatexToken -> String
lexeme (Command xs _)   = xs
lexeme (TextBlock xs _) = xs
lexeme (Blank xs _)     = xs
lexeme (Open Curly _)   = "{"
lexeme (Open Square _)  = "["
lexeme (Close Curly _)  = "}"
lexeme (Close Square _) = "]"

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
                    (match_string "{", (\_ -> return (Just $ Open Curly li))),
                    (match_string "}", (\_ -> return (Just $ Close Curly li))),
                    (match_string "[", (\_ -> return (Just $ Open Square li))),
                    (match_string "]", (\_ -> return (Just $ Close Square li))) ]
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

latex_content :: Scanner LatexToken LatexDoc
latex_content = do
    b  <- is_eof
    li <- get_line_info
    if b
    then return $ Doc [] li
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
                    Doc rest li <- latex_content 
                    return $ Doc (Bracket c0 li0 ct li1:rest) li
            Close _ _ ->         return $ Doc [] li
            Command "\\end" _ -> return $ Doc [] li
            t@(Blank _ _)     -> content_token t
            t@(TextBlock _ _) -> content_token t
            t@(Command _ _)   -> content_token t

content_token :: LatexToken -> Scanner LatexToken LatexDoc
content_token t = do
        read_char
        li    <- get_line_info
        xs    <- latex_content
        case xs of
            Doc (Text y li:ys) li' -> 
                return $ Doc (Text (t:y) li:ys) li'
            Doc xs li' -> 
                return $ Doc (Text [t] li:xs) li'

opt_args :: Scanner LatexToken [[LatexNode]]
opt_args = return []

skip_blank :: Scanner LatexToken ()
skip_blank = do
        xs <- peek
        case xs of
            (Blank _ _:_) -> do read_char ; return ()
            _  -> return ()

argument :: Scanner LatexToken LatexDoc
argument = do
        skip_blank
        xs <- peek
        case xs of
            Open Curly _:_ -> do  
                read_char
                ct <- latex_content
                close <- read_char
                case close of
                    Close Curly _ -> return ct
                    _ -> fail "expecting closing bracket '}'"        
            _ -> fail "expecting opening bracket '{'"            

begin_block :: Scanner LatexToken LatexDoc
begin_block = do
    read_char
    li0 <- get_line_info
--    let li0 = LI fn0 i0 j0 
    args0 <- argument
    ct    <- latex_content
    end   <- read_char
    li1   <- get_line_info
    unless (end == Command "\\end" (line_info end)) $ 
        fail ("expected \\end{" ++ concatMap source (contents' args0) ++ "}, read \'" ++ lexeme end ++ "\'")
    args1 <- argument
    (begin, li2, end, li3) <- 
        case (args0, args1) of
            ( Doc [Text [TextBlock begin li0] _] _ ,
              Doc [Text [TextBlock end li1] _] _ ) -> do
                return (begin, li0, end, li1)
            _  -> fail "name of a begin / end block must be a simple string"    
    unless (begin == end) $ 
        fail (format "begin / end do not match: {0} {1} / {2} {3}" begin li2 end li3)
    Doc rest li <- latex_content 
    return $ Doc (Env begin li0 ct li1:rest) li

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
                            : Open Curly _ 
                            : TextBlock fn _
                            : Close Curly _
                            : _ -> do
                                forM_ [1..4]  $ const $ read_char
                                return fn
                        Open Curly _ 
                            : TextBlock fn _
                            : Close Curly _
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
        

parse_latex_document :: String -> IO (Either [Error] LatexDoc)
parse_latex_document fname = runEitherT $ do
        ys <- EitherT $ scan_doc fname 
        hoistEither $ read_tokens latex_content fname ys (1,1)

latex_structure :: FilePath -> String -> Either [Error] LatexDoc
latex_structure fn xs = do
        ys <- read_lines tex_tokens fn (uncomment xs)
        read_tokens latex_content fn ys (1,1)

is_prefix :: Eq a => [a] -> [a] -> Bool
is_prefix xs ys = xs == take (length xs) ys

uncomment :: String -> String
uncomment xs = unlines $ map (takeWhile ('%' /=)) $ lines xs

with_print :: Show a => a -> a
with_print x = unsafePerformIO (do putStrLn $ show x ; return x)

remove_ref :: String -> String
remove_ref ('\\':'r':'e':'f':'{':xs) = remove_ref xs
remove_ref ('}':xs) = remove_ref xs
remove_ref (x:xs)   = x:remove_ref xs
remove_ref []       = []

type T = State LineInfo

makeTexDoc :: [T LatexNode] -> LatexDoc
makeTexDoc cmd = evalState (do
    xs <- sequence cmd
    li <- get
    return $ Doc xs li) (LI "" 1 1)

addCol :: Int -> LineInfo -> LineInfo
addCol n (LI fn i j) = LI fn i (j+n)

env :: String -> [T LatexNode] -> T LatexNode
env name xs = do
    li  <- get
    modify $ addCol (length $ "\\begin{" ++ name ++ "}")
    ys  <- sequence xs
    li' <- get
    modify $ addCol (length $ "\\end{" ++ name ++ "}")
    return $ Env name li (Doc ys li') li'

bracket :: BracketType -> [T LatexNode] -> T LatexNode
bracket b xs = do
    li  <- get
    modify $ addCol 1
    ys  <- sequence xs
    li' <- get
    modify $ addCol 1
    return $ Bracket b li (Doc ys li') li'

text :: [T LatexToken] -> T LatexNode
text xs = do
    ys <- sequence xs
    li <- get
    return $ Text ys li

tokens :: (a -> LineInfo -> LatexToken) 
       -> a -> T LatexToken
tokens f x = do
    li@(LI fn i _) <- get
    let y = f x li
        ys = lexeme y
        ln = lines ys
        zs = zip ln $ li : [ LI fn (i+k) 1 | k <- [1..]]
        zs' = [ LI fn i (length xs + j) | (xs,LI fn i j) <- zs ]
    put $ lastDef li zs'
    return y

command :: String -> T LatexToken
command = tokens Command

textBlock :: String -> T LatexToken
textBlock = tokens TextBlock

blank :: String -> T LatexToken
blank = tokens Blank

open  :: BracketType -> T LatexToken
open = tokens Open

close :: BracketType -> T LatexToken
close = tokens Close

