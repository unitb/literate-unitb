{-# LANGUAGE TypeFamilies
    , DeriveGeneric
    , TemplateHaskell
    , FlexibleInstances
    , DeriveDataTypeable 
    , TypeSynonymInstances
    , MultiParamTypeClasses
    #-}
module Latex.Parser where

    -- Modules
import Latex.Scanner 

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Lens  hiding (argument)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Either as E
import Control.Monad.Trans.State

import Data.Char
import Data.Either
import qualified Data.Foldable as F
import Data.Function
import Data.Graph
import Data.List ( intercalate )
import qualified Data.List as L
import Data.Map as M hiding ( foldl, map, null, size )
import Data.Semigroup
import Data.Typeable

import GHC.Generics

import Safe

import System.Directory
import System.IO.Unsafe
import System.FilePath

--import Text.Printf

import Utilities.Format
import Utilities.Graph hiding ( map, empty, size )
import Utilities.Lines as LN
import Utilities.Syntactic
--import Utilities.Zipper as Z
--import Utilities.Trace

data LatexNode = 
        Env LineInfo String LineInfo LatexDoc LineInfo
        | Bracket BracketType LineInfo LatexDoc LineInfo
        | Text LatexToken
    deriving (Eq,Show,Generic,Typeable)

data LatexDoc = Doc LineInfo [LatexNode] LineInfo
    deriving (Eq,Show,Generic,Typeable)

data BracketType = Curly | Square
    deriving (Eq,Show,Typeable)

data LatexToken =
        Command String LineInfo
        | TextBlock String LineInfo
        | Blank String LineInfo
        | Open BracketType LineInfo
        | Close BracketType LineInfo
    deriving (Eq, Show, Typeable)

makePrisms ''LatexToken

--instance Zippable LatexNode where
--    type ZipperImpl LatexNode = MZipperT LatexNode LatexDoc

--instance Zippable LatexDoc where
--    type ZipperImpl LatexDoc = MZipperT LatexDoc LatexNode

instance Semigroup LatexDoc where
    (<>) (Doc li0 xs _) (Doc _ ys li1) = Doc li0 (xs++ys) li1

class Convertible a where
    flatten :: a -> String

flatten' :: LatexDoc -> String
flatten' (Doc _ xs _) = concatMap flatten xs

instance Convertible LatexDoc where
    flatten = flatten'

instance Convertible LatexNode where
    flatten (Env _ s _ ct _) = 
               "\\begin{" ++ s ++ "}"
            ++ flatten' ct
            ++ "\\end{" ++ s ++ "}"
    flatten (Bracket b _ ct _) = [openBracket b] ++ flatten' ct ++ [closeBracket b]
    flatten (Text xs) = lexeme xs

instance Convertible StringLi where
    flatten (StringLi xs _) = map fst xs

instance IsBracket BracketType Char where
    bracketPair Curly = ('{','}')
    bracketPair Square = ('[',']')

whole_line :: LineInfo -> [LineInfo]
whole_line (LI fn i j) = map (uncurry3 LI) $ zip3 (repeat fn) (repeat i) [j..]

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x,y,z) = f x y z

flatten_li' :: LatexDoc -> StringLi
flatten_li' (Doc _ xs li) = StringLi (concatMap flatten_li xs) li

getString :: StringLi -> [(Char,LineInfo)]
getString (StringLi xs _) = xs

flatten_li :: LatexNode -> [(Char,LineInfo)]
flatten_li (Env li0 s _ ct li1) = 
           zip ("\\begin{" ++ s ++ "}") (whole_line li0)
        ++ getString (flatten_li' ct)
        ++ zip ("\\end{" ++ s ++ "}") (whole_line li1)
flatten_li (Text xs)        = lexeme_li xs
flatten_li (Bracket b li0 ct li1) 
        = (openBracket b,li0) : getString (flatten_li' ct) ++ [(closeBracket b,li1)]

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

asSingleton :: LatexDoc -> Maybe LatexNode
asSingleton (Doc _ [x] _) = Just x
asSingleton (Doc _ _ _) = Nothing

contents :: LatexNode -> LatexDoc
contents (Env _ _ _ c _)     = c
contents (Bracket _ _ c _) = c
contents (Text t)          = Doc (line_info t) [] (line_info t)
    -- error? li is actually the beginning of the text. Or is it?

contents' :: LatexDoc -> [LatexNode]
contents' (Doc _ xs _) = xs

unconsTex :: LatexDoc -> Maybe (LatexNode,LatexDoc)
unconsTex (Doc _ (x:xs) li) = Just (x,Doc (headDef li $ map line_info xs) xs li)
unconsTex (Doc _ [] _)      = Nothing

consTex :: LatexNode -> LatexDoc -> LatexDoc
consTex x (Doc _ xs li) = Doc (line_info x) (x:xs) li

--instance Show LatexNode where
--    show (Env b _ xs _) = "Env{" ++ b ++ "} (" ++ show (length $ contents' xs) ++ ")"
--    show (Text xs _)    = "Text (" ++ show (take 10 xs) ++ "...)"
--    show (Bracket Curly _ c _)  = "Bracket {" ++ show c ++ "} "
--    show (Bracket Square _ c _) = "Bracket [" ++ show c ++ "] "

--instance Show LatexDoc where
--    show (Doc xs _) = show xs

open_bracket :: BracketType -> Char
open_bracket Curly  = '{'
open_bracket Square = '['

close_bracket :: BracketType -> Char
close_bracket Curly  = '}'
close_bracket Square = ']'

instance Syntactic LatexToken where
    line_info (Command _ li)    = li
    line_info (TextBlock _ li)  = li
    line_info (Blank _ li)      = li
    line_info (Open _ li)       = li
    line_info (Close _ li)      = li

instance Syntactic LatexNode where
    line_info (Env li _ _ _ _)     = li
    line_info (Bracket _ li _ _) = li
    line_info (Text t)           = line_info t

instance Syntactic (TokenStream a) where
    line_info (StringLi xs li) = headDef li (map snd xs)

instance Syntactic LatexDoc where
    line_info (Doc li _ _) = li

tokens :: LatexDoc -> [(LatexToken,LineInfo)]
tokens (Doc _ xs _) = concatMap f xs
    where
        f :: LatexNode -> [(LatexToken,LineInfo)]
        f (Env li0 name li1 ct li2) = f begin ++ cont ++ f end
            where
                f = map (id &&& line_info)
                openLI = li0 & column %~ (length "\\begin"+)
                closeLI = li1 & column %~ (length name+)
                endLI = afterLast (closeLI & column %~ (1+)) cont
                openLI' = endLI & column %~ (length "\\end"+)
                closeLI' = li2 & column %~ (length name+)
                begin = [ (Command "\\begin" li0)
                        , (Open Curly openLI)
                        , (TextBlock name li1) 
                        , (Close Curly closeLI)]
                cont = tokens ct
                end  = [ (Command "\\end" endLI)
                       , (Open Curly openLI')
                       , (TextBlock name li2) 
                       , (Close Curly closeLI')]
        f (Bracket br li0 ct li1) = [(Open br li0,li0)] ++ tokens ct ++ [(Close br li1,li1)]
        f (Text tok) = [(tok,line_info tok)]

source :: LatexNode -> String
source (Text t) = lexeme t
source x           = show x

instance Token LatexToken where
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
        (do guard (not $ L.null xs)
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
            case c of
                Just x  -> do
                    --traceM $ show x
                    --b <- is_eof
                    --when b $ do
                    --    traceM "eof"
                    --    traceM.show =<< peek
                    xs <- tex_tokens
                    --traceM $ "> " ++ show x
                    return ((x,li):xs)
                Nothing -> do
                    li <- get_line_info
                    d  <- read_char
                    --traceM $ show d
                    xs <- tex_tokens
                    --traceM $ "> " ++ show d
                    case xs of
                        (TextBlock ys _,_):zs -> 
                            return ((TextBlock (d:ys) li,li):zs)
                        _ ->return ((TextBlock [d] li,li):xs)

latex_content :: Scanner LatexToken LatexDoc
latex_content = do
    b  <- is_eof
    li <- get_line_info
    if b
    then return $ Doc li [] li
    else do
        c:_ <- peek
        --traceM $ format "latex_content: {0}" c
        case c of
            Command "\\begin" _ -> do
                    begin_block
            Open c0 _ -> do
                    li0 <- get_line_info
                    read_char
                    ct  <- latex_content
                    li1 <- get_line_info
                    c   <- read_char
                    case c of
                        Close c1 _ -> do
                            unless (c0 == c1) $ fail "mismatched brackets"
                        _ -> fail "expected closing bracket"
                    Doc _ rest li' <- latex_content 
                    return $ Doc li (Bracket c0 li0 ct li1:rest) li'
            Close _ _ ->         do
                return $ Doc li [] li
            Command "\\end" _ -> return $ Doc li [] li
            t@(Blank _ _)     -> do
                content_token t
            t@(TextBlock _ _) -> do
                content_token t
            t@(Command _ _)   -> do
                content_token t

content_token :: LatexToken -> Scanner LatexToken LatexDoc
content_token t = do
        read_char
        consTex (Text t) <$> latex_content
        --case xs of
        --    Doc _ (Text y:ys) li' -> 
        --        return $ Doc li (Text (t:y) li:ys) li'
        --    Doc _ xs li' -> 
        --        return $ Doc li (Text t li:xs) li'

size :: LatexDoc -> Int
size (Doc _ xs _) = sum $ map f xs
    where
        f (Text _) = 1
        f (Env _ _ _ ct _) = 1 + size ct
        f (Bracket _ _ ct _) = 1 + size ct

subtrees :: LatexDoc -> [() -> LatexDoc]
subtrees (Doc li xs li') = concatMap f xs ++ ys
    where
        f (Text _) = []
        f (Env li0 n li1 ct li2) = (\() -> ct) : concat [ [ doc, \() -> Doc li [Env li0 n li1 (doc ()) li2] li' ] | doc <- subtrees ct ]
        f (Bracket b li1 ct li2) = (\() -> ct) : concat [ [ doc, \() -> Doc li [Bracket b li1 (doc ()) li2] li' ] | doc <- subtrees ct ]
        g t@(Text _) = [\() -> Doc li [t] li']
        g (Env li0 n li1 ct li2) = [\() -> Doc li [Env li0 n li1 ct li2] li']
        g (Bracket b li1 ct li2) = [\() -> Doc li [Bracket b li1 ct li2] li']
        ys
            | length xs <= 1 = []
            | otherwise      = concatMap g xs


opt_args :: Scanner LatexToken [[LatexNode]]
opt_args = return []

trim_blank_text' :: LatexDoc -> LatexDoc
trim_blank_text' xs = Doc li0 xs' (lis !! length xs')
    where
        Doc li0 ys li = drop_blank_text' xs
        ys' = scanr (\x -> (allBlank x &&)) True ys
        xs' = map fst $ takeWhile (not . snd) $ zip ys ys'
        allBlank (Text (Blank _ _)) = True
        allBlank _ = False
        --isBlank (Blank _ _) = True
        --isBlank _ = False
        lis = map line_info ys ++ [li]

drop_blank_text :: [LatexNode] -> [LatexNode]
drop_blank_text ( Text (Blank _ _) : ys ) = drop_blank_text ys
--drop_blank_text ( Text (Blank _ _ : xs) li : ys ) = drop_blank_text ( Text xs li : ys )
drop_blank_text xs = xs

drop_blank_text' :: LatexDoc -> LatexDoc
drop_blank_text' doc = maybe doc (uncurry drop_blank_text_aux) $ unconsTex doc
    where
        --drop_blank_text_aux :: 
        --drop_blank_text_aux li ( Text [] _ : ys ) = drop_blank_text_aux li ys
        drop_blank_text_aux (Text (Blank _ _)) ys = maybe ys (uncurry drop_blank_text_aux) $ unconsTex ys
        --drop_blank_text_aux _ ( Text (Blank _ li : xs) li' : ys ) = drop_blank_text_aux li ( Text xs li' : ys )
        drop_blank_text_aux x xs = consTex x xs

skip_blank :: Scanner LatexToken ()
skip_blank = do
        xs <- peek
        case xs of
            (Blank _ _:_) -> do read_char ; return ()
            _  -> return ()

argument :: Scanner LatexToken (LineInfo,LatexDoc)
argument = do
        skip_blank
        xs <- peek
        case xs of
            Open Curly _:_ -> do  
                read_char
                li <- get_line_info
                ct <- latex_content
                close <- read_char
                case close of
                    Close Curly _ -> return (li,ct)
                    _ -> fail "expecting closing bracket '}'"        
            _ -> fail "expecting opening bracket '{'"            

begin_block :: Scanner LatexToken LatexDoc
begin_block = do
    liBegin <- get_line_info
    read_char
    --li0 <- get_line_info
--    let li0 = LI fn0 i0 j0 
    (li0,args0) <- argument
    ct    <- latex_content
    end   <- read_char
    unless (end == Command "\\end" (line_info end)) $ 
        fail ("expected \\end{" ++ concatMap source (contents' args0) ++ "}, read \'" ++ lexeme end ++ "\'")
    (li1,args1) <- argument
    (begin, li2, end, li3) <- 
        case (args0, args1) of
            ( Doc _ [Text (TextBlock begin li0)] _ ,
              Doc _ [Text (TextBlock end li1)] _ ) -> do
                return (begin, li0, end, li1)
            _  -> fail "name of a begin / end block must be a simple string"    
    unless (begin == end) $ 
        fail (format "begin / end do not match: {0} {1} / {2} {3}" begin li2 end li3)
    Doc _ rest li <- latex_content 
    return $ Doc liBegin (Env liBegin begin li0 ct li1:rest) li

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
                                replicateM_ 4 read_char
                                return fn
                        Open Curly _ 
                            : TextBlock fn _
                            : Close Curly _
                            : _ -> do
                                replicateM_ 3 read_char
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

fill_holes :: String -> Map String [DocWithHoles] 
           -> Either [Error] [(LatexToken,LineInfo)]
fill_holes fname m = do
        m <- foldM propagate M.empty order
        return (m M.! fname)
    where
        propagate :: (Map String [(LatexToken, LineInfo)])
                  -> SCC String
                  -> Either [Error] (Map String [(LatexToken, LineInfo)])
        propagate m1 (AcyclicSCC v) = Right (insert v (g (m M.! v) m1) m1)
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
        h m (Left (name,_)) = m M.! name
        msg = "A cycle exists in the LaTeX document structure: {0}"
        order = cycles_with [fname] edges 
        edges :: [(String,String)]
        edges    = concatMap f $ toList m
        f (x,ys) = [ (x,y) | y <- map fst $ lefts ys ]
        --m ! x = case M.lookup x m of
        --            Just y  -> y
        --            Nothing -> error $ 
        --                "Map.!: given key is not an element in the map: " 
        --                ++ show x ++ " - " ++ show (keys m) ++ " - " ++ show order

scan_doc :: String -> IO (Either [Error] [(LatexToken,LineInfo)])
scan_doc fname = runEitherT $ do
    let dir = takeDirectory fname
    fname  <- liftIO $ canonicalizePath fname
    (m,xs) <- flip execStateT (M.empty,[(fname,(LI fname 1 1))]) 
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
                                    else lift $ E.left 
                                        [ Error ("file '" ++ path ++ "' does not exist") 
                                            $ LI x i j]
                                path <- liftIO $ canonicalizePath path
                                return $ Left (path,li))
                            (return . Right) path
                    put (insert x ct m,xs ++ lefts ct)
                else put (m,xs)
                rec
            [] -> return ()
    unless (L.null xs) $ error "scan_doc: xs should be null"
    hoistEither $ fill_holes fname m
        

parse_latex_document :: String -> IO (Either [Error] LatexDoc)
parse_latex_document fname = runEitherT $ do
        ys <- EitherT $ scan_doc fname 
        hoistEither $ read_tokens latex_content fname ys (1,1)

latex_structure :: FilePath -> String -> Either [Error] LatexDoc
latex_structure fn xs = do
        ys <- scan_latex fn xs
        read_tokens latex_content fn ys (1,1)

scan_latex :: FilePath -> String -> Either [Error] [(LatexToken,LineInfo)]
scan_latex fn xs = -- trace (printf "input: %s\nuncomment: %s\n" xs cs) $ 
        read_lines tex_tokens fn (uncomment xs)
    --where cs = uncomment xs

is_prefix :: Eq a => [a] -> [a] -> Bool
is_prefix xs ys = xs == take (length xs) ys

uncomment :: String -> String
uncomment xs = F.concat $ fmap removeComment $ LN.lines' xs
    where
        removeComment = uncurry (++) . second (dropWhile (`notElem` "\n\r")) . span ('%' /=)

with_print :: Show a => a -> a
with_print x = unsafePerformIO (do putStrLn $ show x ; return x)

remove_ref :: String -> String
remove_ref ('\\':'r':'e':'f':'{':xs) = remove_ref xs
remove_ref ('}':xs) = remove_ref xs
remove_ref (x:xs)   = x:remove_ref xs
remove_ref []       = []

type T = State LineInfo

--makeTexDoc :: [T LatexNode] -> LatexDoc
--makeTexDoc cmd = evalState (do
--    xs <- sequence cmd
--    li <- get
--    return $ Doc xs li) (LI "" 1 1)

addCol :: Int -> LineInfo -> LineInfo
addCol n (LI fn i j) = LI fn i (j+n)

--env :: String -> [T LatexNode] -> T LatexNode
--env name xs = do
--    li  <- get
--    modify $ addCol (length $ "\\begin{" ++ name ++ "}")
--    ys  <- sequence xs
--    li' <- get
--    modify $ addCol (length $ "\\end{" ++ name ++ "}")
--    return $ Env name li (Doc ys li') li'

--bracket :: BracketType -> [T LatexNode] -> T LatexNode
--bracket b xs = do
--    li  <- get
--    modify $ addCol 1
--    ys  <- sequence xs
--    li' <- get
--    modify $ addCol 1
--    return $ Bracket b li (Doc ys li') li'

--text :: [T LatexToken] -> T LatexNode
--text xs = do
--    ys <- sequence xs
--    li <- get
--    return $ Text ys li

--tokens :: (a -> LineInfo -> LatexToken) 
--       -> a -> T LatexToken
--tokens f x = do
--    li@(LI fn i _) <- get
--    let y = f x li
--        ys = lexeme y
--        ln = lines ys
--        zs = zip ln $ li : [ LI fn (i+k) 1 | k <- [1..]]
--        zs' = [ LI fn i (length xs + j) | (xs,LI fn i j) <- zs ]
--    put $ lastDef li zs'
--    return y

--command :: String -> T LatexToken
--command = tokens Command

--textBlock :: String -> T LatexToken
--textBlock = tokens TextBlock

--blank :: String -> T LatexToken
--blank = tokens Blank

--open  :: BracketType -> T LatexToken
--open = tokens Open

--close :: BracketType -> T LatexToken
--close = tokens Close

