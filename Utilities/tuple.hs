{-# LANGUAGE TypeOperators, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Utilities.Tuple where

-- import Control.Monad hiding (join)
-- import Control.Monad.State.Class
-- import Control.Monad.Trans
-- import Control.Monad.Trans.Maybe
-- import Control.Monad.Trans.State (State,evalState)

-- import Data.List
-- import Data.List.Utils
-- import Data.Typeable

-- import System.Directory
-- import System.Environment
-- import System.FilePath

-- import Text.Printf

infixr 5 :+:

data (:+:) a b = (:+:) a b

-- class AsTuple a where
--     data Tuple a :: *
--     toTuple :: a -> Tuple a
--     fromTuple :: Tuple a -> a

-- instance AsTuple () where
--     data Tuple () = UnitTuple ()
--     toTuple () = UnitTuple ()
--     fromTuple (UnitTuple ()) = ()

-- instance AsTuple (a,b) where
--     func = 

-- data Remainder = Remainder [String]

type family StringTuple a :: *
type instance StringTuple () = ()
type instance StringTuple (a :+: as) = (String :+: (StringTuple as))

class Tuple a where
    tLength :: a -> Int

instance Tuple () where
    tLength _ = 0

instance Tuple as => Tuple (a :+: as) where
    tLength _ = tLength (error "tuple.tLength" :: as) + 1

-- class ArgList a where
--     parse' :: MaybeT (State [String]) a
--     display' :: a -> [String]
--     arbitrary :: a

-- instance ArgList Remainder where
--     parse' = do
--         xs <- lift get
--         lift $ put []
--         return $ Remainder xs
--     display' (Remainder xs) = [show $ typeOf xs]
--     arbitrary = Remainder []

-- instance ArgList () where
--     parse' = MaybeT $ do
--         xs <- get
--         if null xs 
--             then return $ Just ()
--             else return $ Nothing
--     display' () = []
--     arbitrary = ()

-- instance (Typeable a, Read a, ArgList as) => ArgList (a :+: as) where
--     parse' = do
--         ys <- lift $ get
--         x  <- case ys of
--             y:ys -> 
--                 case (reads y,cast y) of
--                         (_,Just y) -> do
--                             put ys
--                             return y
--                         ([(r,"")],_) -> do
--                             put ys
--                             return r
--                         _ -> fail ""
--             _ -> fail ""
--         xs <- parse'
--         return $ x :+: xs
--     display' (x :+: xs) = show (typeOf x) : display xs
--     arbitrary = undefined :+: arbitrary

-- class ArgList a => StringList (StringTuple a) where

-- instance 

-- parse :: ArgList a => [String] -> Maybe a
-- parse xs = evalState (runMaybeT parse') xs

-- parseArgs :: forall a. (ArgList a) => String -> MaybeT IO a
-- parseArgs prog = MaybeT $ do
--     let argType = intercalate " " $ display (arbitrary :: a)
--         usage   = printf "usage: %s %s\n" prog argType
--     xs <- getArgs
--     case parse xs of
--         Just x -> return $ Just x
--         Nothing -> do
--             usage
--             return Nothing

-- parseArgs' :: forall a. (ArgList a) => String -> StringTuple a -> MaybeT IO a
-- parseArgs' prog desc = MaybeT $ do
--     let argType = intercalate " " $ display (arbitrary :: a)
--         usage   = printf "usage: %s %s\n" prog argType
--     xs <- getArgs
--     case parse xs of
--         Just x -> return $ Just x
--         Nothing -> do
--             usage
--             return Nothing

-- checkIO :: IO Bool -> String -> MaybeT IO ()
-- checkIO cond msg = do
--     b <- lift cond
--     unless b $ do
--         lift $ putStrLn $ "*** ERROR ***"
--         lift $ putStrLn msg
--         fail ""

-- check :: Bool -> String -> MaybeT IO ()
-- check b msg = checkIO (return b) msg

-- finally :: MaybeT IO a -> IO () -> MaybeT IO a
-- finally cmd fin = MaybeT $ do
--         x <- runMaybeT cmd
--         fin
--         return x

-- ensureDir :: FilePath -> IO ()
-- ensureDir path = do
--     b <- doesDirectoryExist path
--     unless b $ do
--         ensureDir $ takeDirectory path
--         createDirectory path

-- run :: Monad m => MaybeT m a -> m ()
-- run cmd = runMaybeT cmd >> return ()
