{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DefaultSignatures      #-}
module Logic.Expr.Classes where

import Control.Monad.Reader
import Control.Monad.State

import Data.Data
import Data.List
import Data.List.Utils
import Data.Maybe
import Data.Tuple

class Named n where
    name    :: n -> String
    as_pair :: n -> (String, n)
    as_pair n = (name n, n)
    
    decorated_name :: n -> String
    decorated_name x = runReader (decorated_name' x) ProverOutput

    decorated_name' :: n -> Reader OutputMode String

    z3_name :: n -> String
    z3_name x = z3_escape (name x)

data OutputMode = ProverOutput | UserOutput

newtype Endo m a = Endo { fromEndo :: a -> m a }

class Tree a where
    as_tree   :: a -> StrList
    as_tree'  :: a -> Reader OutputMode StrList
    rewriteM' :: Monad m => (b -> a -> m (b,a)) -> b -> a -> m (b,a)
    rewrite'  :: (b -> a -> (b,a)) -> b -> a -> (b,a)
    as_tree x = runReader (as_tree' x) ProverOutput
    default rewriteM' :: (Monad m, Data a) => (b -> a -> m (b,a)) -> b -> a -> m (b,a)
    rewriteM' f x t = liftM swap $ runStateT (gmapM (wrap g) t) x
        where
            g x y = liftM swap $ f y x
                -- (Endo return) (gcast $ Endo $ \x -> StateT $ liftM swap . flip f x)

    rewrite' f x t = (rewriteM' g x t) ()
        where
            g x t () = f x t

wrap :: (Monad m, Typeable a, Typeable d) 
     => (a -> b -> m (a,b)) 
     -> d -> StateT b m d
wrap f = fromEndo $ fromMaybe (Endo return) (gcast $ Endo $ StateT . f)

data StrList = List [StrList] | Str String

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

rewriteM :: (Monad m, Tree a) => (a -> m a) -> a -> m a
rewriteM f t = do
        ((),x) <- rewriteM' g () t
        return x
    where 
        g () x = do
            y <- f x
            return ((),y)

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
