{-# LANGUAGE RecordWildCards #-}
module Interactive.Pipeline 
--    ( run_pipeline )
where

    -- Modules
--import Browser
    
import Document.Document

import Interactive.Observable
import Interactive.Serialize

import Logic.Label

import UnitB.AST
import UnitB.PO

import Z3.Z3 
        ( discharge
        , Validity ( .. ) )

    -- Libraries
import Control.Concurrent

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import           Data.Char
import           Data.Map as M 
                    ( Map
                    , insert, keys
                    , fromList
                    , toList, unions )
import qualified Data.Map as M 

--import Foreign

import System.Directory
import System.Console.ANSI
import System.TimeIt

import Utilities.Format
import Utilities.Syntactic
--import Utilities.Trace

    -- The pipeline is made of three processes:
    --  o the parser
    --  o the prover
    --  o the display
    --
    -- The prover and the parser _share_ a map of proof obligations
    -- The prover and the parser _share_ a list of PO labels
    -- The 
    
wait :: Monad m => m Bool -> m ()
wait m = do
        b <- m
        if b 
            then return ()
            else wait m
            
data Shared = Shared
        { working    :: Observable Int
        , system     :: Observable System
        , error_list :: Observable [Error]
        , pr_obl     :: Observable (Map (Label,Label) (Seq,Maybe Bool))
        , fname      :: FilePath
        , exit_code  :: MVar ()
        , parser_state :: Observable ParserState
        }

data ParserState = Idle Double | Parsing
    deriving (Eq, Show)

parser :: Shared
       -> IO (IO ())
parser (Shared { .. })  = return $ do
        t <- getModificationTime fname
        write_obs parser_state Parsing
        (dt,()) <- timeItT $ parse
        write_obs parser_state (Idle dt)
        evalStateT (forever $ do
            liftIO $ do
                threadDelay 5000000
            t0 <- get
            t1 <- liftIO $ getModificationTime fname
            if t0 == t1 then return ()
            else do
                put t1
                liftIO $ do
                    write_obs parser_state Parsing
                    (t,()) <- timeItT $ parse
                    write_obs parser_state (Idle t)
            ) t
    where
        f m = do
            x <- proof_obligation m
            return $ fromList $ map (g $ _name m) $ toList $ x
        g lbl (x,y) = ((lbl,x),y)
        parse = do
                xs <- liftIO $ runEitherT $ do
                    s  <- EitherT $ parse_system fname
                    ms <- hoistEither $ mapM f $ M.elems $ machines s
                    pos <- hoistEither $ mapM theory_po $ M.elems $ theories s
                    let cs = M.fromList $ map (uncurry g) $ do
                                (x,ys) <- zip (map label (keys $ theories s)) pos
                                y <- toList ys
                                return (x,y)
                    return (ms, cs, s)
                case xs of
                    Right (ms,cs,s) -> do
                        let new_pos = unions (cs : ms) :: Map Key Seq
                            f (s0,b0) (s1,b1)
                                | s0 == s1  = (s0,b0)
                                | otherwise = (s1,b1)
                            g s = (s, Nothing)
                        write_obs system s
                        write_obs error_list []
                        modify_obs pr_obl $ \pos -> do
                            return $ M.unionWith f (pos `M.intersection` new_pos) (M.map g new_pos)
                        return ()
                    Left es   -> do
                        write_obs error_list es
                        return ()

prover :: Shared -> IO (IO ())
prover (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    req <- newEmptyMVar
    forM_ [1..8] $ \p -> forkOn p $ worker req 
    return $ forever $ do
        takeMVar tok
        inc 200
        po <- read_obs pr_obl
        forM_ (keys po) $ \k -> do
            po <- reads_obs pr_obl $ M.lookup k
            case po of
                Just (po,Nothing) -> do
                    liftIO $ putMVar req (k,po)
                _               -> return ()
        dec 200
    where
        inc x = modify_obs working (return . (+x))
        dec x = modify_obs working (return . (+ (-x)))            
        worker req = forever $ do
            (k,po) <- takeMVar req
            inc 1
            r      <- discharge po
            dec 1
            modify_obs pr_obl $ return . insert k (po,Just $ r == Valid)

proof_report :: Map (Label,Label) (Seq,Maybe Bool) 
             -> [Error] -> Bool 
             -> [String]
proof_report outs es b = xs ++ 
                     ( if null es then []
                       else "> errors" : map report es ) ++
                     [ if b
                       then "> working ..."
                       else ""
                     ] 
    where
        xs = concatMap f (toList outs)
        f ((m,lbl),(_,r))
            | r == Just False = [format " x {0} - {1}" m lbl]
--            | r == Just True  = [format "   {0} - {1}" m lbl]
            | otherwise = []

run_all :: [IO (IO ())] -> IO [ThreadId]
run_all xs = do
        ys <- sequence xs
        mapM f ys
    where
        f cmd = forkIO $ cmd

display :: Shared
        -> IO (IO ())
display (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    observe error_list tok
    observe working tok
    observe parser_state tok
    clearScreen
    return $ forever $ do
            outs <- read_obs pr_obl
            es   <- read_obs error_list
            w    <- read_obs working
            let ys = proof_report outs es (w /= 0)
            cursorUpLine $ length ys
            clearFromCursorToScreenBeginning
            forM_ ys $ \x -> do
                let lns = lines x
                forM_ lns $ \x -> do
                    putStr x
                    clearFromCursorToLineEnd 
                    putStrLn ""
            st <- read_obs parser_state
            putStr $ format "n workers: {0} parser: {1}" w st
            clearFromCursorToLineEnd 
            putStrLn ""
            threadDelay 500000
            takeMVar tok

serialize :: Shared -> IO (IO ())
serialize (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    return $ forever $ do
        threadDelay 10000000
        takeMVar tok
        pos <- read_obs pr_obl
        let out = pos
--        (pos@(out,_),es) <- takeMVar ser
        es <- read_obs error_list
        dump_pos fname pos
        dump_z3 fname pos
        writeFile 
            (fname ++ ".report") 
            (unlines $ proof_report out es False)

summary :: Shared -> IO (IO ())
summary (Shared { .. }) = do
        v <- newEmptyMVar
        observe system v
        return $ forever $ do
            threadDelay 10000000
            takeMVar v
            s <- read_obs system
            produce_summaries s

keyboard :: Shared -> IO ()
keyboard sh@(Shared { .. }) = do
        xs <- getLine
        if map toLower xs == "quit" 
        then return ()
        else if map toLower xs == "reset" then do
            modify_obs pr_obl $ \m -> 
                return $ M.map (\(x,_) -> (x,Nothing)) m
            keyboard sh
        else do
            putStrLn $ format "Invalid command: '{0}'" xs
            keyboard sh

run_pipeline :: FilePath -> IO ()
run_pipeline fname = do
        system     <- new_obs empty_system
        working    <- new_obs 0
        error_list <- new_obs []
        exit_code  <- newEmptyMVar 
        m          <- load_pos fname M.empty
        pr_obl     <- new_obs m
        parser_state <- new_obs (Idle 0)
        let sh = Shared { .. }
        ts <- run_all 
            [ summary sh
            , prover sh -- (M.map f m)
            , serialize sh
            , parser sh
            , display sh 
            ]
        keyboard sh
        putStrLn "received a 'quit' command"
        mapM_ killThread ts
--        return sh

--type Verifier = StablePtr (Shared)

--
----run_verifier :: CString -> IO Verifier
----run_verifier fname = do
----    fname <- peekCString fname
----    sh <- run_pipeline fname
----    newStablePtr sh
--
----            merr <- gets error_msg
----            mpos <- gets failed_po
----            liftIO $ swapMVar mpos $ concatMap g $ toList res
----        g ((x,y),(p,b))
----            | not b     = [Ref fname (show y) (1,1)]
----            | otherwise = []
--
--get_error_list :: Verifier -> IO CErrList
--get_error_list v = do
--        Shared { .. } <- deRefStablePtr v
--        err <- read_obs error_list
--        let xs = map f err
--        r  <- newIORef (RL [] xs)
--        newStablePtr r
--    where
--        f (Error x (LI fname i j)) = Ref fname x (i,j)
--
--get_proof_obligations :: Verifier -> IO CErrList
--get_proof_obligations v = do
--        Shared { .. } <- deRefStablePtr v
--        pos <- read_obs pr_obl
--        let ys = concatMap (g fname) $ toList pos
--        r  <- newIORef (RL [] ys)
--        newStablePtr r
--    where
--        g fname ((_,y),(_,b))
--            | b == Just False = [Ref fname (show y) (1,1)]
--            | otherwise       = []
