module Document.Tests.Suite where

    -- Modules
import Document.Machine

import Logic.Expr
import Logic.Proof

import UnitB.AST
import UnitB.PO as PO

import Z3.Z3

    -- Libraries

import Control.Arrow hiding (right,left)
import Control.Concurrent
import Control.Exception

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either

import Data.List as L
import Data.Map as M
import Data.Time

import Utilities.Format
import Utilities.Syntactic

import System.Directory
import System.IO.Unsafe

type POS a = Either [Error] (Map String (a, Map Label Sequent))

pos :: MVar (Map FilePath ((POS Machine,POS Theory), UTCTime))
pos = unsafePerformIO $ newMVar M.empty

list_file_obligations' :: FilePath -> IO (POS Machine,POS Theory)
list_file_obligations' path = do
    path <- canonicalizePath path
    t <- getModificationTime path
    m <- takeMVar pos
    case path `M.lookup` m of
        Just (r,t') 
            | t' == t -> do
                putMVar pos m
                return r
        _ -> do
            sys <- parse_system path
            let cmd :: Monad m => (b -> m c) -> a -> b -> m (b,c)
                cmd f _ = runKleisli (Kleisli return &&& Kleisli f)
                -- ms :: Either 
                ms = fmap machines sys >>= traverseWithKey (cmd PO.proof_obligation)
                ts = fmap theories sys >>= traverseWithKey (cmd theory_po)
            putMVar pos $ M.insert path ((ms,ts),t) m
            return (ms,ts)

verify :: FilePath -> Int -> IO (String, Map Label Sequent)
verify path i = do
    r <- fst `liftM` list_file_obligations' path
    case r of
        Right ms -> do
            let (m,pos) = snd $ i `elemAt` ms
            r <- try (str_verify_machine m)
            case r of
                Right (s,_,_) -> return (s, pos)
                Left e -> return (show (e :: SomeException),pos)
        Left x -> return (unlines $ L.map show x, empty)

proof_obligation :: FilePath -> String -> Int -> IO String
proof_obligation path lbl i = eitherT (return . show) return $ do
        xs <- bimapEitherT show id
            $ EitherT $ fst `liftM` list_file_obligations' path
        let pos = snd $ snd $ i `elemAt` xs
        po <- maybe 
                (left $ format "invalid label: {0}" lbl)
                right
            $ label lbl `M.lookup` pos
        let cmd = concatMap pretty_print' $ z3_code po
        return cmd

find_errors :: FilePath -> IO String 
find_errors path = do
    m <- fst `liftM` list_file_obligations' path
    return $ either 
        (unlines . L.map show) 
        (const $ "no errors")
        m

parse_machine :: FilePath -> Int -> IO (Either [Error] Machine)
parse_machine path n = fmap (!! n) `liftM` parse path

parse :: FilePath -> IO (Either [Error] [Machine])
parse path = do
    (fmap (elems . M.map fst) . fst) `liftM` list_file_obligations' path

verify_thy :: FilePath -> String -> IO (String,Map Label Sequent)
verify_thy path name = do
        r <- runEitherT $ do
            r <- EitherT $ snd `liftM` list_file_obligations' path
            let pos = snd $ r ! name
            res <- lift $ verify_all pos
            return (unlines $ L.map (\(k,r) -> success r ++ show k) $ toList res, pos)
        case r of
            Right r -> do
                return r
            Left x -> return (show x, M.empty)
    where
        success True  = "  o  "
        success False = " xxx "
