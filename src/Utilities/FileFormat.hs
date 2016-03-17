{-# LANGUAGE TypeFamilies #-}
module Utilities.FileFormat where

import Codec.Compression.Zlib
import Control.Exception
import Control.Lens
import Control.Monad.Trans
import Control.Monad.Trans.Either

import qualified Data.ByteString as Strict
import qualified Data.ByteString.Lazy as Lazy
import Data.Either.Combinators
import Data.Serialize

type FileFormat a = FileFormat' () a

data FileFormat' err a = FileFormat 
    { writeFormat :: FilePath -> a -> IO () 
    , readFormat'  :: FilePath -> IO (Either err a)
    }

readFormat :: FileFormat a
           -> FilePath
           -> IO (Maybe a)
readFormat ff = fmap rightToMaybe . readFormat' ff

newtype CompressedByteString = Compressed { getCompressed :: Lazy.ByteString }
    deriving (Serialize)

instance Wrapped CompressedByteString where
    type Unwrapped CompressedByteString = Lazy.ByteString
    _Wrapped' = iso getCompressed Compressed

{-# INLINABLE readWrite #-}
readWrite :: FileFormat' err a
          -> FileFormat' err a
          -> FileFormat' err a
readWrite (FileFormat _ r) (FileFormat w _) = FileFormat w r

{-# INLINABLE compressIso #-}
compressIso :: Prism' CompressedByteString Lazy.ByteString
compressIso = iso (decompress . getCompressed) (Compressed . compress)

{-# INLINABLE prismFormat' #-}
prismFormat' :: (a -> err)
             -> Prism' a b 
             -> FileFormat' err a
             -> FileFormat' err b
prismFormat' err pr (FileFormat w r) = FileFormat ((. view (re pr)) . w) (fmap (>>= readF) . r)
    where
        readF = mapLeft err . matching pr

{-# INLINABLE prismFormat #-}
prismFormat :: Prism' a b 
            -> FileFormat a
            -> FileFormat b
prismFormat = prismFormat' (const ())

{-# INLINABLE prismSerialize #-}
prismSerialize :: Serialize a => Prism' Strict.ByteString a
prismSerialize = prism encode (\s -> either (const $ Left s) Right $ decode s)

{-# INLINABLE prismSerializeLazy #-}
prismSerializeLazy :: Serialize a => Prism' Lazy.ByteString a
prismSerializeLazy = prism encodeLazy (\s -> either (const $ Left s) Right $ decodeLazy s)

{-# INLINABLE serialized #-}
serialized :: Serialize a
           => FileFormat Strict.ByteString 
           -> FileFormat a
serialized = prismFormat prismSerialize

{-# INLINABLE serialized' #-}
serialized' :: Serialize a
            => err
            -> FileFormat' err Strict.ByteString
            -> FileFormat' err a
serialized' err = prismFormat' (const err) prismSerialize

{-# INLINABLE serializedLazy #-}
serializedLazy :: Serialize a
               => FileFormat Lazy.ByteString 
               -> FileFormat a
serializedLazy = prismFormat prismSerializeLazy

{-# INLINABLE serializedLazy' #-}
serializedLazy' :: Serialize a
                => err
                -> FileFormat' err Lazy.ByteString
                -> FileFormat' err a
serializedLazy' err = prismFormat' (const err) prismSerializeLazy

{-# INLINABLE compressed #-}
compressed :: FileFormat Lazy.ByteString 
           -> FileFormat Lazy.ByteString
compressed = compressed' ()

{-# INLINABLE compressed' #-}
compressed' :: err
            -> FileFormat' err Lazy.ByteString
            -> FileFormat' err Lazy.ByteString
compressed' err = prismFormat' (const err) (from _Wrapped'.compressIso)

{-# INLINABLE stringFile #-}
stringFile :: FileFormat' err String
stringFile = FileFormat writeFile (fmap Right . readFile)

{-# INLINABLE strictByteStringFile #-}
strictByteStringFile :: FileFormat' err Strict.ByteString
strictByteStringFile = FileFormat Strict.writeFile (fmap Right . Strict.readFile)

{-# INLINABLE lazyByteStringFile #-}
lazyByteStringFile :: FileFormat' err Lazy.ByteString
lazyByteStringFile = FileFormat Lazy.writeFile (fmap Right . Lazy.readFile)

{-# INLINABLE stringFile' #-}
stringFile' :: FileFormat' err String
stringFile' = stringFile

{-# INLINABLE strictByteStringFile' #-}
strictByteStringFile' :: FileFormat' err Strict.ByteString
strictByteStringFile' = strictByteStringFile

{-# INLINABLE lazyByteStringFile' #-}
lazyByteStringFile' :: FileFormat' err Lazy.ByteString
lazyByteStringFile' = lazyByteStringFile

{-# INLINABLE failOnException #-}
failOnException :: FileFormat a 
                -> FileFormat a 
failOnException = failOnException' ()

{-# INLINABLE failOnException' #-}
failOnException' :: err 
                 -> FileFormat' err a 
                 -> FileFormat' err a 
failOnException' err (FileFormat w r) = FileFormat w readF
    where
      readF fn = do
            let handler e@(SomeException _) = do
                    print e
                    return $ Left err
            handle handler $ runEitherT $ do
                x <- EitherT $ r fn
                lift $ evaluate x
                return x


