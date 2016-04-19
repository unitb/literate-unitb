module Utilities.FileSystem 
    ( FileSystem (..)
    , FileSystemM
    , unFileSystemM
    , FS
    , runFS, mockFS
    , MockFileSystem
    , NoParam(..)
    , OneParam(..)
    , MockFileSystemState
    , MockFileSystemState' (..)
    , ifFileExists'
    , files
    , module System.Directory 
    , runMockFileSystem
    , execMockFileSystem
    , evalMockFileSystem
    , runMockFileSystem'
    , execMockFileSystem'
    , evalMockFileSystem'
    )
where

import Control.Lens
import Control.Invariant
import Control.Monad.State
import Control.Precondition

import Data.Default
import Data.Map as M hiding ((!))

import Prelude hiding (readFile,writeFile)
import qualified Prelude as P

import System.Directory hiding 
            ( createDirectoryIfMissing
            , doesDirectoryExist
            , doesFileExist)
import qualified System.Directory as D
import System.FileLock
import System.FilePath

newtype ExistingFile s = ExistingFile FilePath

newtype NoParam r m = NoParam { getNoParam :: m r }
newtype OneParam a r m = OneParam { getOneParam :: (forall s. ExistingFile s -> m a) -> m r }

type FS a = forall m. FileSystem m => m a
newtype FileSystemM a = FileSystemM { unFileSystemM :: FS a } 
    deriving (Functor)

mockFS :: FileSystemM a -> State MockFileSystemState a
mockFS (FileSystemM (MockFileSystem m)) = m

runFS :: FileSystemM a -> IO a
runFS = unFileSystemM

class Monad m => FileSystem m where
    {-# MINIMAL liftFS, lift2FS | 
        readFile, writeFile
        , createDirectoryIfMissing
        , ifFileExists, doesFileExist
        , doesDirectoryExist #-}
    readFile  :: ExistingFile s -> m String
    readFile fn = getNoParam $ liftFS (NoParam $ readFile fn)
    writeFile :: Pre => FilePath -> String -> m ()
    writeFile fn xs = getNoParam $ liftFS (NoParam $ writeFile fn xs)
    ifFileExists :: FilePath -> (forall s. ExistingFile s -> m a) -> m (Maybe a) 
    ifFileExists fn = getOneParam $ lift2FS (OneParam $ ifFileExists fn)
    createDirectoryIfMissing :: Bool -> FilePath -> m ()
    createDirectoryIfMissing b fn = getNoParam $ liftFS (NoParam $ createDirectoryIfMissing b fn)
    doesDirectoryExist :: FilePath -> m Bool
    doesDirectoryExist fn = getNoParam $ liftFS (NoParam $ doesDirectoryExist fn)
    doesFileExist :: FilePath -> m Bool
    doesFileExist fn = getNoParam $ liftFS (NoParam $ doesFileExist fn)
    liftFS :: Pre 
           => (forall m0. (Pre, FileSystem m0) => NoParam a m0) 
           -> NoParam a m
    liftFS f = f
    lift2FS :: Pre 
            => (forall m0. (Pre, FileSystem m0) => OneParam a r m0) 
            -> OneParam a r m
    lift2FS f = f

ifFileExists' :: FileSystem m
              => FilePath -> a 
              -> (forall s. ExistingFile s -> m a) 
              -> m a
ifFileExists' fn x cmd = fromMaybe x <$> ifFileExists fn cmd

instance Applicative FileSystemM where
    pure x = FileSystemM $ pure x
    {-# INLINE (<*>) #-}
    FileSystemM f <*> FileSystemM x = FileSystemM $ f <*> x
instance Monad FileSystemM where
    {-# INLINE (>>=) #-}
    FileSystemM m >>= f = FileSystemM $ m >>= unFileSystemM . f
instance FileSystem FileSystemM where
    {-# INLINE liftFS #-}
    liftFS f = NoParam $ FileSystemM $ getNoParam f
    {-# INLINE lift2FS #-}
    lift2FS f = OneParam $ \g -> FileSystemM $ getOneParam f $ \x -> (unFileSystemM $ g x)

instance FileSystem IO where
    readFile (ExistingFile fn) = do
        P.readFile fn
    writeFile = P.writeFile
    ifFileExists fn cmd = do
        b <- doesFileExist fn
        if b then do
            Just <$> withFileLock fn Shared (const $ cmd $ ExistingFile fn)
        else do
            return Nothing
    createDirectoryIfMissing = D.createDirectoryIfMissing
    doesDirectoryExist = D.doesDirectoryExist
    doesFileExist = D.doesFileExist

newtype MockFileSystem a = MockFileSystem 
        (State MockFileSystemState a)
    deriving (Functor,Applicative,Monad)

newtype MockFileSystemState' = MockFileSystemState 
        { _files :: Map FilePath (Maybe String) }
    deriving (Show)

type MockFileSystemState = Checked MockFileSystemState'

makeLenses ''MockFileSystemState'

instance HasInvariant MockFileSystemState' where
    invariant m = do        
        "inv0" ## foldMapWithKey 
            (\f _ -> f ## takeDirectory f `M.lookup` (m^.files) === Just Nothing) 
            (m^.files)
        "has current directory" ## "." `M.lookup` (m^.files) === Just Nothing
        "has root" ## "/" `M.lookup` (m^.files) === Just Nothing

instance FileSystem MockFileSystem where
    readFile (ExistingFile fn) = MockFileSystem $ fromJust' <$> uses' files (! fn)
    writeFile fn x = do
        dirExists  <- doesDirectoryExist (takeDirectory fn)
        isDir      <- doesDirectoryExist fn
        MockFileSystem $ mutate' $ do 
            providedM (dirExists && not isDir)  $
                files %= insert fn (Just x)
    ifFileExists fn f = do
            exists <- doesFileExist fn
            if exists
                then Just <$> f (ExistingFile fn)
                else return Nothing
    doesFileExist fn = MockFileSystem $ 
            (Just True ==).fmap isJust <$> uses' files (fn `M.lookup`)
    doesDirectoryExist fn = MockFileSystem $ 
            (Just True ==).fmap isNothing <$> uses' files (fn `M.lookup`)
    createDirectoryIfMissing b fn = do
            exists <- doesDirectoryExist (takeDirectory fn)
            providedM (b || exists) $ do
                MockFileSystem $ mutate' $ do
                    let ds 
                            | b         = takeWhile (`notElem` [".","/"]) $ iterate takeDirectory fn
                            | otherwise = [fn]
                    files %= union (fromList $ (,Nothing) <$> ds)

emptyFSState :: MockFileSystemState 
emptyFSState = create' $ do
        files .= fromList [(".",Nothing),("/",Nothing)]

instance Default MockFileSystemState' where
    def = emptyFSState^.content'

runMockFileSystem :: FileSystemM a -> (a,MockFileSystemState)
runMockFileSystem cmd = runMockFileSystem' cmd emptyFSState
evalMockFileSystem :: FileSystemM a -> a
evalMockFileSystem = fst . runMockFileSystem
execMockFileSystem :: FileSystemM a -> MockFileSystemState
execMockFileSystem = snd . runMockFileSystem

runMockFileSystem' :: FileSystemM a -> MockFileSystemState -> (a,MockFileSystemState)
runMockFileSystem' (FileSystemM (MockFileSystem cmd)) = runState cmd
evalMockFileSystem' :: FileSystemM a -> MockFileSystemState -> a
evalMockFileSystem' (FileSystemM (MockFileSystem cmd)) = evalState cmd
execMockFileSystem' :: FileSystemM a -> MockFileSystemState -> MockFileSystemState
execMockFileSystem' (FileSystemM (MockFileSystem cmd)) = execState cmd
