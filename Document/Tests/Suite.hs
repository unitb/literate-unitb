module Document.Tests.Suite where

    -- Modules
import Document.Document as Doc

import Logic.Expr
import Logic.Proof

import UnitB.AST
import UnitB.PO as PO

import Z3.Z3

    -- Libraries
import Control.Applicative ((<$>))
import Control.Arrow hiding (right,left)
import Control.Concurrent
import Control.Exception

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
    do
            sys <- parse_system path
            let cmd :: Monad m => (b -> m c) -> a -> b -> m (b,c)
                cmd f _ = runKleisli (Kleisli return &&& Kleisli f)
                -- ms :: Either 
                ms = fmap machines sys >>= traverseWithKey (cmd PO.proof_obligation)
                ts = fmap theories sys >>= traverseWithKey (cmd theory_po)
            putMVar pos $ M.insert path ((ms,ts),t) m
            return (ms,ts)

verify :: FilePath -> Int -> IO (String, Map Label Sequent)
verify path i = makeReport' empty $ do
    ms <- EitherT $ fst <$> list_file_obligations' path
    if i < size ms then do
            let (m,pos) = snd $ i `elemAt` ms
            r <- lift $ try (str_verify_machine m)
            case r of
                Right (s,_,_) -> return (s, pos)
                Left e -> return (show (e :: SomeException),pos)
    else return (format "accessing {0}th refinement out of {1}" i (size ms),empty)

all_proof_obligations :: FilePath -> IO (Either String [Map Label String])
all_proof_obligations path = runEitherT $ do
        xs <- bimapEitherT show id
            $ EitherT $ fst <$> list_file_obligations' path
        let pos = M.elems $ M.map snd xs
            cmd = L.map (M.map $ unlines . L.map pretty_print' . z3_code) pos
        return cmd

raw_proof_obligation :: FilePath -> String -> Int -> IO String
raw_proof_obligation path lbl i = makeReport $ do
        ms <- EitherT $ Doc.parse_machine path
        let po = raw_machine_pos (ms !! i) ! label lbl
            cmd = unlines $ L.map pretty_print' $ z3_code po
        return $ format "; {0}\n{1}; {2}\n" lbl cmd lbl

proof_obligation :: FilePath -> String -> Int -> IO String
proof_obligation path lbl i = makeReport $ do
        xs <- EitherT $ fst <$> list_file_obligations' path
        if i < size xs then do
            let pos = snd $ snd $ i `elemAt` xs
            case label lbl `M.lookup` pos of
                Just po -> do
                    let cmd = unlines $ L.map pretty_print' $ z3_code po
                    return $ format "; {0}\n{1}; {2}\n" lbl cmd lbl
                Nothing ->
                    return $ format "invalid label: {0}\n{1}" lbl $ 
                        unlines $ L.map show $ keys pos
        else
            return $ format "accessing {0}th refinement out of {1}" i (size xs)            

find_errors :: FilePath -> IO String 
find_errors path = do
    m <- fst <$> list_file_obligations' path
    return $ either 
        (unlines . L.map report) 
        (const $ "no errors")
        m

parse_machine :: FilePath -> Int -> IO (Either [Error] Machine)
parse_machine path n = fmap (!! n) <$> parse path

parse :: FilePath -> IO (Either [Error] [Machine])
parse path = do
    (fmap (elems . M.map fst) . fst) <$> list_file_obligations' path

verify_thy :: FilePath -> String -> IO (String,Map Label Sequent)
verify_thy path name = makeReport' empty $ do
        r <- EitherT $ snd <$> list_file_obligations' path
        let pos = snd $ r ! name
        res <- lift $ try (verify_all pos)
        case res of
            Right res -> return (unlines $ L.map (\(k,r) -> success r ++ show k) $ toList res, pos)
            Left e -> return (show (e :: SomeException),pos)
    where
        success True  = "  o  "
        success False = " xxx "

get_system :: FilePath -> EitherT String IO System
get_system path = do
    EitherT $ either (Left . show_err) Right 
        <$> parse_system path

