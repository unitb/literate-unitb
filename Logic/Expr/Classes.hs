module Logic.Expr.Classes where

import Control.Lens hiding (List,rewriteM)
import Control.Monad.Reader
import Control.Monad.State

import Data.Data
import Data.Data.Lens 
import Data.List
import Data.List.Utils
import Data.Tuple
import Data.Typeable.Lens

class HasName a n | a -> n where
    name :: Getter a String

class HasName n String => Named n where
    --name    :: n -> String
    as_pair :: n -> (String, n)
    as_pair n = (n^.name, n)
    
    decorated_name :: n -> String
    decorated_name x = runReader (decorated_name' x) ProverOutput

    decorated_name' :: n -> Reader OutputMode String

    z3_name :: n -> String
    z3_name x = z3_escape (x^.name)

data OutputMode = ProverOutput | UserOutput

newtype Endo m a = Endo { fromEndo :: a -> m a }

class Tree a where
    as_tree   :: a -> StrList
    as_tree'  :: a -> Reader OutputMode StrList
    as_tree x = runReader (as_tree' x) ProverOutput
    rewrite'  :: (b -> a -> (b,a)) -> b -> a -> (b,a)
    rewriteM :: (Applicative m, Tree a) => (a -> m a) -> a -> m a
    default rewriteM :: (Applicative m, Data a) => (a -> m a) -> a -> m a
    rewriteM f t = gtraverse (_cast f) t
        where
                -- (Endo return) (gcast $ Endo $ \x -> StateT $ liftM swap . flip f x)

    rewrite' f x t = (rewriteM' g x t) ()
        where
            g x t () = f x t

rewriteM' :: (Monad m, Tree a) => (b -> a -> m (b,a)) -> b -> a -> m (b,a)
rewriteM' f x t = swap <$> runStateT (rewriteM (StateT . fmap (fmap swap) . flip f) t) x

instance Tree () where
    as_tree' () = return $ List []
    rewriteM f = f

data StrList = List [StrList] | Str String

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

fold_mapM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
fold_mapM _ s [] = return (s,[])
fold_mapM f s0 (x:xs) = do
        (s1,y)  <- f s0 x
        (s2,ys) <- fold_mapM f s1 xs
        return (s2,y:ys)

fold_map :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
fold_map _ s [] = (s,[])
fold_map f s0 (x:xs) = (s2,y:ys)
    where
        (s1,y)  = f s0 x
        (s2,ys) = fold_map f s1 xs

visit :: Tree a => (b -> a -> b) -> b -> a -> b
visit f s x = fst $ rewrite' g s x
    where
        g s0 y = (f s0 y, y)

rewrite :: Tree a => (a -> a) -> a -> a
rewrite f x = snd $ rewrite' g () x
    where
        g () x = ((), f x)

visitM :: (Monad m, Tree a) => (b -> a -> m b) -> b -> a -> m b
visitM f x t = visit g (return x) t
    where
        g x t = do
            y <- x
            f y t

class FromList a b where
    from_list :: a -> [b] -> b

instance FromList a a where
    from_list x [] = x
    from_list _ _  = error "from_list: too many arguments"

instance FromList a b => FromList (b -> a) b where
    from_list f (x:xs) = from_list (f x) xs
    from_list _ [] = error "from_list: not enough arguments"

z3_escape :: String -> String
z3_escape xs = intercalate "sl@" $ split "\\" xs
