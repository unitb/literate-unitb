module Tools.BuildSystem 
    ( didAnythingChange
    , set_extensions
    , init_state )
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State hiding ( State )
import Control.Monad.Trans.Writer

import Data.Map hiding ( map )
import Data.Time

import System.Directory
import System.FilePath.Posix

data State = State 
    { timestamps :: Map FilePath UTCTime
    , extensions :: [String]
    }

init_state :: State
init_state = State empty [".hs",".lhs"]

get_files :: MonadIO m
          => FilePath -> WriterT [FilePath] (StateT State m) ()
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

set_extensions :: Monad m
               => [String] -> StateT State m ()
set_extensions exts = modify $ \s -> s { extensions = exts }

didAnythingChange :: (MonadIO m) => StateT State m Bool
didAnythingChange = do
        old_files <- gets timestamps
        files <- get_time_stamps
        modify $ \s -> s { timestamps = files }
        return $ files /= old_files
