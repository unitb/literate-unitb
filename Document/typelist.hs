{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Document.TypeList where

    -- Modules 
import Latex.Parser

import Utilities.Syntactic

    -- Libraries
import Control.Monad.Reader.Class
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

class Readable a where
    read_args :: (Monad m, MonadReader (Int,Int) m)
              => StateT [LatexDoc] (EitherT [Error] m) a

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