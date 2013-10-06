module BuildSystem 
    ( didAnythingChange
    , set_extensions
    , init_state )
where

import Control.Concurrent.Thread.Delay
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State hiding ( State )
import Control.Monad.Trans.Writer

import Data.Map hiding ( map )
import Data.Time
import Data.Time.Clock

import System.Directory
import System.FilePath.Posix
import System.Locale
import System.Process

data State = State 
    { timestamps :: Map FilePath UTCTime
    , extensions :: [String]
    }

init_state = State empty [".hs",".lhs"]

get_files path = do
        xs <- liftIO $ getDirectoryContents path
        let ys = map (combine path) xs
        subdirs <- flip filterM ys $ \f -> do
            b <- liftIO $ doesDirectoryExist f
            return $ b && not (takeFileName f `elem` [".",".."])
        exts <- lift $ gets extensions
        forM_ ys $ \f -> do
            if takeExtension f `elem` exts
                then tell [f]
                else return ()
        forM_ subdirs get_files


get_time_stamps :: (MonadIO m) => StateT State m (Map FilePath UTCTime)
get_time_stamps = do
        files <- execWriterT $ get_files "."
        ts <- forM files $ liftIO . getModificationTime
        return $ fromList $ zip files ts

set_extensions exts = modify $ \s -> s { extensions = exts }

didAnythingChange :: (MonadIO m) => StateT State m Bool
didAnythingChange = do
        old_files <- gets timestamps
        files <- get_time_stamps
        modify $ \s -> s { timestamps = files }
--        let us = 
        return $ files /= old_files
