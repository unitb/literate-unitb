{-# LANGUAGE TypeFamilies #-}
module Latex.Parser where

    -- Modules
import Latex.Scanner 

    -- Libraries
import Control.Applicative hiding ((<|>))
import Control.Arrow
import Control.DeepSeq
import Control.Lens  hiding (argument)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Either as E
import Control.Precondition

import Data.Char
import Data.Either
import Data.Either.Combinators
import qualified Data.Foldable as F
import Data.Graph
import Data.List ( intercalate )
import qualified Data.List as L
import Data.Map as M hiding ( foldl, map, null, size, (!) )
import Data.Semigroup
import Data.String.Lines as LN
import Data.Typeable

import GHC.Generics (Generic)

import Safe

import System.Directory
import System.IO.Unsafe
import System.FilePath

import Text.Parsec ((<?>),(<|>))
import qualified Text.Parsec as P
import Text.Parsec.Error
import qualified Text.Parsec.Pos as P

import Text.Printf.TH

import Utilities.Graph hiding ( map, empty, size, (!) )
import Utilities.Syntactic

data LatexNode = 
        EnvNode Environment
        | BracketNode Bracket
        | Text LatexToken
    deriving (Eq,Show,Generic,Typeable)

data Environment = Env LineInfo String LineInfo LatexDoc LineInfo
    deriving (Eq,Show,Generic,Typeable)

data Bracket = Bracket BracketType LineInfo LatexDoc LineInfo
    deriving (Eq,Show,Generic,Typeable)

data LatexDoc = Doc LineInfo [LatexNode] LineInfo
    deriving (Eq,Show,Generic,Typeable)

data BracketType = Curly | Square
    deriving (Eq,Show,Typeable,Generic)

data LatexToken =
        Command String LineInfo
        | TextBlock String LineInfo
        | Blank String LineInfo
        | Open BracketType LineInfo
        | Close BracketType LineInfo
    deriving (Eq, Show, Typeable, Generic)

makePrisms ''LatexToken

envType :: Environment -> String
envType (Env _ n _ _ _) = n

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
    flatten (EnvNode (Env _ s _ ct _)) = 
               "\\begin{" ++ s ++ "}"
            ++ flatten' ct
            ++ "\\end{" ++ s ++ "}"
    flatten (BracketNode (Bracket b _ ct _)) = [openBracket b] ++ flatten' ct ++ [closeBracket b]
    flatten (Text xs) = lexeme xs

instance Convertible [LatexToken] where
    flatten = concatMap lexeme

instance Convertible [(LatexToken,LineInfo)] where
    flatten = concatMap (lexeme.fst)

instance Convertible StringLi where
    flatten (StringLi xs _) = map fst xs

instance IsBracket BracketType Char where
    bracketPair Curly = ('{','}')
    bracketPair Square = ('[',']')

instance NFData Environment where
instance NFData Bracket where
instance NFData LatexDoc where
instance NFData LatexNode where
instance NFData LatexToken where
instance NFData BracketType where

lineInfoLens :: Lens' LatexToken LineInfo
lineInfoLens f (TextBlock x li) = TextBlock x <$> f li
lineInfoLens f (Command x li) = Command x <$> f li
lineInfoLens f (Blank x li) = Blank x <$> f li
lineInfoLens f (Open x li)  = Open x  <$> f li
lineInfoLens f (Close x li) = Close x <$> f li

whole_line :: LineInfo -> [LineInfo]
whole_line (LI fn i j) = map (uncurry3 LI) $ zip3 (repeat fn) (repeat i) [j..]

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x,y,z) = f x y z

flatten_li' :: LatexDoc -> StringLi
flatten_li' (Doc _ xs li) = StringLi (concatMap flatten_li xs) li

getString :: StringLi -> [(Char,LineInfo)]
getString (StringLi xs _) = xs

flatten_li :: LatexNode -> [(Char,LineInfo)]
flatten_li (EnvNode (Env li0 s _ ct li1)) = 
           zip ("\\begin{" ++ s ++ "}") (whole_line li0)
        ++ getString (flatten_li' ct)
        ++ zip ("\\end{" ++ s ++ "}") (whole_line li1)
flatten_li (Text xs)        = lexeme_li xs
flatten_li (BracketNode (Bracket b li0 ct li1)) 
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

class IsLatexNode node where
    contents :: node -> LatexDoc

instance IsLatexNode Bracket where
    contents (Bracket _ _ c _) = c
instance IsLatexNode Environment where
    contents (Env _ _ _ c _) = c
instance IsLatexNode LatexToken where
    contents t = Doc (line_info t) [] (line_info t)
    -- error? li is actually the beginning of the text. Or is it?

instance IsLatexNode LatexNode where
    contents (EnvNode c)       = contents c
    contents (BracketNode c)   = contents c
    contents (Text t)          = contents t

contents' :: LatexDoc -> [LatexNode]
contents' (Doc _ xs _) = xs

unconsTex :: LatexDoc -> Maybe (LatexNode,LatexDoc)
unconsTex (Doc _ (x:xs) li) = Just (x,Doc (headDef li $ map line_info xs) xs li)
unconsTex (Doc _ [] _)      = Nothing

consTex :: LatexNode -> LatexDoc -> LatexDoc
consTex x (Doc _ xs li) = Doc (line_info x) (x:xs) li

prependNodes :: [LatexNode] -> LatexDoc -> LatexDoc
prependNodes ns d = L.foldr consTex d ns

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
    after x = end (x,line_info x)
    traverseLineInfo = lineInfoLens

instance Syntactic LatexNode where
    line_info (EnvNode (Env li _ _ _ _))     = li
    line_info (BracketNode (Bracket _ li _ _)) = li
    line_info (Text t)           = line_info t
    after (Text t) = after t
    after (EnvNode (Env _ nm _ _ li))  = end (nm ++ "}",li)
    after (BracketNode (Bracket _ _ _ li)) = end ("}",li)
    traverseLineInfo f (BracketNode (Bracket b li0 ct li1)) = fmap BracketNode $
            Bracket b <$> f li0 
                      <*> traverseLineInfo f ct 
                      <*> f li1
    traverseLineInfo f (EnvNode (Env li0 n li1 ct li2)) = fmap EnvNode $
            Env <$> f li0
                <*> pure n
                <*> f li1
                <*> traverseLineInfo f ct
                <*> f li2
    traverseLineInfo f (Text t) = Text <$> lineInfoLens f t

instance Syntactic LatexDoc where
    line_info (Doc li _ _) = li
    after (Doc _ _ li)     = li
    traverseLineInfo f (Doc li xs li') = 
            Doc <$> f li 
                <*> traverse (traverseLineInfo f) xs 
                <*> f li'

tokens :: LatexDoc -> [(LatexToken,LineInfo)]
tokens (Doc _ xs _) = concatMap f xs
    where
        f :: LatexNode -> [(LatexToken,LineInfo)]
        f (EnvNode (Env li0 name li1 ct li2)) = f begin ++ cont ++ f end
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
        f (BracketNode (Bracket br li0 ct li1)) = [(Open br li0,li0)] ++ tokens ct ++ [(Close br li1,li1)]
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
                    xs <- tex_tokens
                    return ((x,li):xs)
                Nothing -> do
                    li <- get_line_info
                    d  <- read_char
                    xs <- tex_tokens
                    case xs of
                        (TextBlock ys _,_):zs -> 
                            return ((TextBlock (d:ys) li,li):zs)
                        _ ->return ((TextBlock [d] li,li):xs)

type Parser = P.Parsec [LatexToken] ()

posToLi :: P.SourcePos -> LineInfo
posToLi pos = LI <$> P.sourceName <*> P.sourceLine <*> P.sourceColumn $ pos

liToPos :: LineInfo -> P.SourcePos
liToPos li = P.newPos (li^.filename) (li^.line) (li^.column)

latex_content' :: Parser LatexDoc
latex_content' = do
        Doc <$> lineInfo
            <*> P.many node
            <*> lineInfo
    where
        node  = (env <|> brackets <|> text) <?> "node"
        env   = do
            li0 <- lineInfo
            cmd "\\begin"          <?> "begin environment"
            (n,li1) <- argument    <?> "argument"
            ct  <- latex_content'
            cmd "\\end"            <?> [printf|end keyword (%s)|] n
            (_,li2) <- argument' n <?> [printf|\\end{%s}|] n
            return $ EnvNode $ Env li0 n li1 ct li2
        brackets = do
            li0 <- lineInfo
            b   <- open <?> "open bracket"
            ct  <- latex_content'
            li1 <- lineInfo
            close b  <?> "close bracket"
            return $ BracketNode $ Bracket b li0 ct li1
        text  = fmap Text $ 
                    (texToken' (_Command . notEnv) <?> "command")
                <|> (texToken' _Blank     <?> "space")
                <|> (texToken' _TextBlock <?> "text")
        notEnv f (x,li)
            | x `notElem` ["\\begin","\\end"] = f (x,li)
            | otherwise                       = pure (x,li)
        open     = texToken (_Open._1)
        close b  = texToken (_Close._1.only b)
        argument = argumentAux id
        argument' n = argumentAux (only n)
        argumentAux :: Show a => Prism' String a -> Parser (a,LineInfo)
        argumentAux p = do
            optional $ texToken _Blank
            texToken (_Open._1.only Curly)    <?> "open curly"
            li  <- lineInfo
            arg <- texToken (_TextBlock._1.p) <?> "argument"
            texToken (_Close._1.only Curly)   <?> "close curly"
            return (arg,li)
        lineInfo = posToLi <$> P.getPosition
        cmd x  = texToken (_Command._1.only x)

texToken :: (Traversal' LatexToken a) -> Parser a
texToken = token 

token :: (Syntactic token,P.Stream xs Identity token,Show token,Token token)
      => (Traversal' token a) -> P.Parsec xs () a
token p = tokenAux (^? p)

texTokenAux :: (LatexToken -> Maybe a) -> Parser a
texTokenAux = tokenAux

tokenAux :: (Syntactic token,P.Stream xs Identity token,Show token,Token token)
         => (token -> Maybe a) -> P.Parsec xs () a
tokenAux p = P.tokenPrim show (const (\t -> const $ liToPos $ end (t,line_info t)) . posToLi) p

token' :: (Syntactic token,P.Stream xs Identity token,Show token,Token token)
       => (Traversal' token a) -> P.Parsec xs () token
token' p = tokenAux (\x -> x <$ (x^?p))

texToken' :: (Traversal' LatexToken a) -> Parser LatexToken
texToken' p = texTokenAux (\x -> x <$ (x^?p))

latex_content :: FilePath -> [(LatexToken,LineInfo)] -> (Int,Int) -> Either [Error] LatexDoc
latex_content fn toks (i,j) = mapLeft toErr $ P.parse parser fn $ map fst toks
    where toErr e = [Error (errMsg e) (posToLi $ P.errorPos e)]
          errMsg e = intercalate "; " $ L.nub $ concatMap f $ errorMessages e
          f (SysUnExpect xs) = ["unexpected: " ++ xs]
          f (UnExpect xs) = ["unexpected: " ++ xs]
          f (Expect xs)   = ["expected: " ++ xs]
          f (Message xs)  = [xs]
          parser = do
            P.setPosition (P.newPos fn i j)
            x <- latex_content'
            eof
            return x
          eof = P.try (do{ c <- P.try (texToken' id); P.unexpected (lexeme c) }
                                <|> return ()
                                )


size :: LatexDoc -> Int
size (Doc _ xs _) = sum $ map f xs
    where
        f (Text _) = 1
        f (EnvNode (Env _ _ _ ct _)) = 1 + size ct
        f (BracketNode (Bracket _ _ ct _)) = 1 + size ct

subtrees :: LatexDoc -> [() -> LatexDoc]
subtrees (Doc li xs li') = concatMap f xs ++ ys
    where
        f (Text _) = []
        f (EnvNode (Env li0 n li1 ct li2)) = (\() -> ct) : concat 
            [ [ doc, \() -> Doc li [EnvNode $ Env li0 n li1 (doc ()) li2] li' ] 
                | doc <- subtrees ct ]
        f (BracketNode (Bracket b li1 ct li2)) = (\() -> ct) : 
            concat [ 
                [ doc, \() -> Doc li [BracketNode $ Bracket b li1 (doc ()) li2] li' ] 
                    | doc <- subtrees ct ]
        g t@(Text _) = [\() -> Doc li [t] li']
        g (EnvNode (Env li0 n li1 ct li2)) = [\() -> Doc li [EnvNode $ Env li0 n li1 ct li2] li']
        g (BracketNode (Bracket b li1 ct li2)) = [\() -> Doc li [BracketNode $ Bracket b li1 ct li2] li']
        ys
            | length xs <= 1 = []
            | otherwise      = concatMap g xs


opt_args :: Scanner LatexToken [[LatexNode]]
opt_args = return []

trim_blank_text' :: LatexDoc -> LatexDoc
trim_blank_text' xs = Doc li0 xs' (lis ! length xs')
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
        return (m ! fname)
    where
        propagate :: (Map String [(LatexToken, LineInfo)])
                  -> SCC String
                  -> Either [Error] (Map String [(LatexToken, LineInfo)])
        propagate m1 (AcyclicSCC v) = Right (insert v (g (m ! v) m1) m1)
        propagate _ (CyclicSCC xs@(y:_)) = Left 
            [ (Error (msg $ intercalate "," xs) 
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
        msg = [printf|A cycle exists in the LaTeX document structure: %s|]
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
        

parse_latex_document :: FilePath -> IO (Either [Error] LatexDoc)
parse_latex_document fname = runEitherT $ do
        ys <- EitherT $ scan_doc fname 
        hoistEither $ latex_content fname ys (1,1)

latex_structure :: FilePath -> String -> Either [Error] LatexDoc
latex_structure fn xs = do
        ys <- scan_latex fn xs
        latex_content fn ys (1,1)

scan_latex :: FilePath -> String -> Either [Error] [(LatexToken,LineInfo)]
scan_latex fn xs = -- trace ([printf|input: %s\nuncomment: %s\n|] xs cs) $ 
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

addCol :: Int -> LineInfo -> LineInfo
addCol n (LI fn i j) = LI fn i (j+n)

