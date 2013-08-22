module Document where

import Control.Monad.State

import Data.Char
import Data.IORef
import Data.Map as M

import System.IO
import System.IO.Unsafe

liftMS :: (Monad m, Ord k) => v -> StateT v m a -> k -> StateT (Map k v) m a
liftMS y act x = do
        m <- get
        (r,y) <- lift $ runStateT act (maybe y id $ M.lookup x m)
        put (insert x y m)
        return r

data Account = Account { balance :: Int }

withdraw n a 
        | n <= balance a    = a { balance = balance a - n }
        | otherwise         = error "insufficient funds"

perform_withdrawal n = do
        b <- gets balance
        if n <= b
            then modify (withdraw n)
            else liftIO $ putStrLn "not enough money"

data AccID = ID Int

data Bank = Bank { accs :: Map AccID Account }

--withdraw_from n am = do
--        acc <- gets accs
--        if n `member` acc
--        then do

data Tree a = 
    Node3 (Tree a) a (Tree a) a (Tree a) 
    | Node2 (Tree a) a (Tree a) 
    | Leaf            

insert x Leaf = (Node2 Leaf x Leaf,True)
insert x t@(Node2 t0 y t1)
        | x < y && b0     = 
        | x < y && not b0 = Node2 t0' y t1
        | x == y          = (t, False)
        | x > y && b1     = 
        | x > y && not b1 = Node2 t0 y t1'
    where
        (t0', b0)   = insert x t0
        (t1', b1)   = insert x t1

--extract_doc xs = do
--        let p  = filter (\x -> take 2 x == "> " || take 2 x == ">\t")
--        let ls = (map (drop 2) $ p $ lines xs)
--        putStrLn $ unlines ls
--
--data Section = Section String [String]
--    deriving Show
--
--prefix xs ys = xs == take (length xs) ys
--
--data DocPart = Head String | Line String | Trash
--
--keywords = unsafePerformIO $ newIORef [
--    "proof",
--    "event",
--    "machine",
--    "invariant",
--    "property",
--    "element",
--    "variable",
--    "variables",
--    "transient" ]
--
--extract_struct xs = do
--        kw <- readIORef keywords
--        let ys = map (".." ++) kw
--        let ls = lines xs
--        let zs = map (f ys) ls ++ [Trash]
--        let ws = reverse $ fst $ foldl g ([], Nothing) zs
--        return ws
--    where
--        f kw x
--            | any (\y -> prefix y x) kw      = Head x
--            | prefix "\t" x || all isSpace x = Line x
--            | otherwise                      = Trash
--        g x y                             = (sect x y, osect x y)
--        sect (xs, Just (x, ys)) (Line s)  = xs
--        sect (xs, Nothing) _              = xs
--        sect (xs, Just (x, ys)) _         = (Section x $ reverse ys):xs
--        osect (xs, _) (Head s)            = Just (drop 2 s, [])
--        osect (xs, Just (x, ys)) (Line s) = Just (x, (drop 1 s):ys)
--        osect _ _                         = Nothing
--        
-- 
--
--main = do
--        xs <- readFile "doc.lit"
--        extract_doc xs
--        extract_struct xs