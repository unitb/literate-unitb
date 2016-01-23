#!/usr/bin/env runhaskell
module Browser where

import Data.IORef
import Data.List as L

import Foreign 
import Foreign.C.Types
import Foreign.C.String

data Reference = Ref 
    { file_name :: String
    , message :: String
    , line_info :: (Int,Int)
    }

data RefList = RL [Reference] [Reference]

type CErrList = StablePtr (IORef RefList)

error_list :: IO CErrList
error_list = do
        let ref0 = Ref
                    { file_name = "safe.hs"
                    , message = "a problem has been found in \"safe.hs\""
                    , line_info = (50, 15)
                    }
            ref1 = Ref
                    { file_name = "haskell.h"
                    , message = "problem in .h file"
                    , line_info = (15,0)
                    }
        r <- newIORef $ RL [] [ref0,ref1]
        newStablePtr r

free_list :: CErrList -> IO ()
free_list = freeStablePtr

get_file_name :: CErrList -> IO CString
get_file_name sp = do
    r       <- deRefStablePtr sp
    RL _ (ref:_) <- readIORef r
    newCString (file_name ref)

get_message :: CErrList -> IO CString
get_message sp = do
    r       <- deRefStablePtr sp
    RL _ (ref:_) <- readIORef r
    newCString (message ref)

get_line_number :: CErrList -> IO CInt
get_line_number sp = do
    r       <- deRefStablePtr sp
    RL _ (ref:_) <- readIORef r
    return (fromIntegral $ fst $ line_info ref)

move_forward :: CErrList -> IO ()
move_forward sp = do
    r <- deRefStablePtr sp
    RL xs (y:ys) <- readIORef r
    writeIORef r (RL (y:xs) ys)

off :: CErrList -> IO Bool
off sp = do
    r <- deRefStablePtr sp
    RL _ ys <- readIORef r
    return $ L.null ys

foreign export ccall free_list :: CErrList -> IO ()
foreign export ccall get_file_name :: CErrList -> IO CString
foreign export ccall get_message :: CErrList -> IO CString
foreign export ccall move_forward :: CErrList -> IO ()
foreign export ccall off :: CErrList -> IO Bool
foreign export ccall error_list :: IO CErrList
foreign export ccall get_line_number :: CErrList -> IO CInt
