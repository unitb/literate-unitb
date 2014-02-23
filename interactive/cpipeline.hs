{-# LANGUAGE ForeignFunctionInterface #-}
module Interactive.CPipeline where

import Browser

import Pipeline

import Foreign.C.String

foreign export ccall run_verifier :: CString -> IO Verifier
foreign export ccall get_error_list :: Verifier -> IO CErrList
foreign export ccall get_proof_obligations :: Verifier -> IO CErrList
