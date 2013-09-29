{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Document.TypeList where

    -- Modules 
--import Document.Visitor

import Latex.Parser

import Utilities.Syntactic

    -- Libraries
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import Data.Char

class Readable a where
    read_args :: (Monad m, MonadReader (Int,Int) m)
              => StateT [LatexDoc] (EitherT [Error] m) a

instance Readable [LatexDoc] where
    read_args = do
        ts <- get
        ([arg],ts) <- lift $ cmd_params 1 ts
        put ts
        return arg

instance Readable [Char] where
    read_args = do
        ts <- get
        (arg,ts) <- lift $ get_1_lbl ts
        put ts
        return arg

--     this instance is added to allow
--     a visitor to require the presence of some
--     arguments without using them
--instance Readable () where
--    read_args = do
--        ts <- get
--        (_,ts) <- lift $ cmd_params 1 ts
--        put ts
--        return ()

class TypeList a where
    get_tuple :: (Monad m, MonadReader (Int,Int) m)
              => [LatexDoc] -> EitherT [Error] m (a, [LatexDoc])

instance TypeList () where
    get_tuple = runStateT $ return ()

instance Readable a => TypeList (a,()) where
    get_tuple = runStateT $ do
        x <- read_args 
        return (x,())

instance 
        (Readable a0,Readable a1) 
        => TypeList (a0,a1,())
    where
    get_tuple = runStateT $ do
        x0 <- read_args 
        x1 <- read_args 
        return (x0,x1,())

instance 
        (Readable a0,Readable a1,Readable a2) 
        => TypeList (a0,a1,a2,())
    where
    get_tuple = runStateT $ do
        x0 <- read_args 
        x1 <- read_args 
        x2 <- read_args 
        return (x0,x1,x2,())

instance 
        (Readable a0,Readable a1,Readable a2,Readable a3) 
        => TypeList (a0,a1,a2,a3,())
    where
    get_tuple = runStateT $ do
        x0 <- read_args 
        x1 <- read_args 
        x2 <- read_args 
        x3 <- read_args 
        return (x0,x1,x2,x3,())

instance 
        (Readable a0,Readable a1,Readable a2,Readable a3,Readable a4) 
        => TypeList (a0,a1,a2,a3,a4,())
    where
    get_tuple = runStateT $ do
        x0 <- read_args 
        x1 <- read_args 
        x2 <- read_args 
        x3 <- read_args 
        x4 <- read_args 
        return (x0,x1,x2,x3,x4,())

instance 
        ( Readable a0,Readable a1,Readable a2,Readable a3
        , Readable a4,Readable a5) 
        => TypeList (a0,a1,a2,a3,a4,a5,())
    where
    get_tuple = runStateT $ do
        x0 <- read_args 
        x1 <- read_args 
        x2 <- read_args 
        x3 <- read_args 
        x4 <- read_args 
        x5 <- read_args 
        return (x0,x1,x2,x3,x4,x5,())


instance 
        ( Readable a0,Readable a1,Readable a2,Readable a3
        , Readable a4,Readable a5,Readable a6) 
        => TypeList (a0,a1,a2,a3,a4,a5,a6,())
    where
    get_tuple = runStateT $ do
        x0 <- read_args 
        x1 <- read_args 
        x2 <- read_args 
        x3 <- read_args 
        x4 <- read_args 
        x5 <- read_args 
        x6 <- read_args 
        return (x0,x1,x2,x3,x4,x5,x6,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   ,())
instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8 ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9
                   ,())
instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10
                   ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11
                   ,())
instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12 ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13 
                   ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13,Readable a14 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13,a14 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            x14 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13,x14
                   ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13,Readable a14,Readable a15) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13,a14,a15 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            x14 <- read_args 
            x15 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13,x14,x15
                   ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13,Readable a14,Readable a15
            , Readable a16 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13,a14,a15,a16 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            x14 <- read_args 
            x15 <- read_args 
            x16 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13,x14,x15
                   , x16
                   ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13,Readable a14,Readable a15
            , Readable a16,Readable a17 ) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13,a14,a15,a16,a17 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            x14 <- read_args 
            x15 <- read_args 
            x16 <- read_args 
            x17 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13,x14,x15
                   , x16,x17
                   ,())

instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13,Readable a14,Readable a15
            , Readable a16,Readable a17,Readable a18) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13,a14,a15,a16,a17,a18 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            x14 <- read_args 
            x15 <- read_args 
            x16 <- read_args 
            x17 <- read_args 
            x18 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13,x14,x15
                   , x16,x17,x18
                   ,())
instance 
            ( Readable a0, Readable a1, Readable a2, Readable a3
            , Readable a4, Readable a5, Readable a6, Readable a7
            , Readable a8, Readable a9, Readable a10,Readable a11
            , Readable a12,Readable a13,Readable a14,Readable a15
            , Readable a16,Readable a17,Readable a18,Readable a19) 
        =>  TypeList ( a0, a1, a2, a3, a4, a5, a6, a7, a8, a9
                     , a10,a11,a12,a13,a14,a15,a16,a17,a18,a19 ,())
    where
        get_tuple = runStateT $ do
            x0  <- read_args 
            x1  <- read_args 
            x2  <- read_args 
            x3  <- read_args 
            x4  <- read_args 
            x5  <- read_args 
            x6  <- read_args 
            x7  <- read_args 
            x8  <- read_args 
            x9  <- read_args 
            x10 <- read_args 
            x11 <- read_args 
            x12 <- read_args 
            x13 <- read_args 
            x14 <- read_args 
            x15 <- read_args 
            x16 <- read_args 
            x17 <- read_args 
            x18 <- read_args 
            x19 <- read_args 
            return ( x0, x1, x2, x3, x4, x5, x6, x7
                   , x8, x9, x10,x11,x12,x13,x14,x15
                   , x16,x17,x18,x19
                   ,())

cmd_params :: (Monad m, MonadReader (Int,Int) m)
           => Int -> [LatexDoc] 
           -> EitherT [Error] m ([[LatexDoc]], [LatexDoc])
cmd_params 0 xs     = right ([], xs)
cmd_params n xs     = do
        (i,j) <- lift $ ask
        case drop_blank_text xs of
            Bracket _ _ xs (i,j) : ys -> do
                (ws, zs) <- local (const (i,j)) $ cmd_params (n-1) ys
                right (xs:ws, zs)
            x                 -> left [("bad argument: " ++ show xs,i,j)]

cmd_params_ n xs = fmap fst $ cmd_params n xs

get_1_lbl :: (Monad m, MonadReader (Int,Int) m)
          => [LatexDoc] -> EitherT [Error] m (String, [LatexDoc])
get_1_lbl xs = do 
        ([x],z) <- cmd_params 1 xs
        case trim_blank_text x of
            ([Text [TextBlock x _]]) 
                -> right (x,z)
            ([Text [Command x _]]) 
                -> right (x,z)
            _   -> err_msg (line_info xs)
    where
        err_msg (i,j) = left [("expecting a label",i,j)]
        
get_2_lbl :: (Monad m, MonadReader (Int,Int) m)
          => [LatexDoc] 
          -> EitherT [Error] m (String, String, [LatexDoc])
get_2_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        return (lbl0,lbl1,xs)

get_3_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        (lbl2,xs) <- get_1_lbl xs
        return (lbl0,lbl1,lbl2,xs)

get_4_lbl xs = do
        (lbl0,xs) <- get_1_lbl xs
        (lbl1,xs) <- get_1_lbl xs
        (lbl2,xs) <- get_1_lbl xs
        (lbl3,xs) <- get_1_lbl xs
        return (lbl0,lbl1,lbl2,lbl3,xs)

drop_blank_text :: [LatexDoc] -> [LatexDoc]
drop_blank_text ( Text [Blank _ _] : ys ) = drop_blank_text ys
drop_blank_text ( Text (Blank _ _ : xs) : ys ) = drop_blank_text ( Text xs : ys )
drop_blank_text xs = xs

trim_blank_text xs = reverse $ drop_blank_text (reverse $ drop_blank_text xs)

skip_blanks :: [LatexToken] -> [LatexToken]
skip_blanks (Blank _ _ : xs) = xs
skip_blanks xs = xs 
