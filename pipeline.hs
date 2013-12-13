{-# LANGUAGE RecordWildCards #-}
module Pipeline 
--    ( run_pipeline )
where

    -- Modules
import Browser
    
import Document.Document

import Observable

import Serialize

import UnitB.AST
import UnitB.PO

import Z3.Z3 
        ( discharge
        , Validity ( .. ) )

    -- Libraries
import Control.Concurrent
--import Control.Concurrent.STM.TChan

import Control.Monad
--import Control.Monad.STM
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import           Data.Char
import           Data.IORef
import           Data.Map as M 
                    ( Map
                    , insert, keys
                    , fromList
                    , toList, unions )
import qualified Data.Map as M 
--import           Data.Maybe
import           Data.Set as S 
                    ( Set )

import Foreign
import Foreign.C.String

import System.Directory
import System.Console.ANSI

import Utilities.Format
import Utilities.Syntactic

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
--        { pos     :: MVar (Map (Label,Label) Seq)
--        , tok     :: MVar ()
--        , lbls    :: MVar (Either [Error] (Set (Label,Label)))
--        , status  :: TChan (Label,Label,Seq,Bool)
        { working    :: Observable Int
--        , ser     :: MVar ((Map (Label,Label) (Seq,Bool), Set (Label,Label)),[Error])
        , system     :: Observable System
        , error_list :: Observable [Error]
        , pr_obl     :: Observable (Map (Label,Label) (Seq,Maybe Bool))
        , fname      :: FilePath
        , exit_code  :: MVar ()
        -- , io      :: MVar String
        }
            
data Display = Display
        { result :: Map (Label,Label) (Seq,Bool)
        , labels :: Set (Label,Label)
        , errors :: [Error]
        , error_msg  :: MVar [Reference]
        , failed_po :: MVar [Reference]
        }

--console io = forever $ do
--    xs <- takeMVar io
--    putStrLn xs
            
parser :: Shared
       -> IO ()
parser (Shared { .. })  = do
        liftIO $ putStrLn "parser started"
        t <- getModificationTime fname
        parse
        evalStateT (forever $ do
            liftIO $ threadDelay 1000000
            t0 <- get
            t1 <- liftIO $ getModificationTime fname
            if t0 == t1 then return ()
            else do
                put t1
                liftIO $ putStrLn "parse"
                liftIO $ parse
            ) t
    where
        f m = do
            x <- proof_obligation m
            return $ fromList $ map (g $ _name m) $ toList $ x
        g lbl (x,y) = ((lbl,x),y)
        parse = do
--                ms <- parse_machine fname
                (xs) <- liftIO $ runEitherT $ do
                    s  <- EitherT $ parse_system fname
                    xs <- hoistEither $ mapM f $ M.elems $ machines s
                    return (xs, s)
                case xs of
                    Right (ms,s) -> do
                        let new_pos = unions ms
                            f (s0,b0) (s1,b1)
                                | s0 == s1  = (s0,b0)
                                | otherwise = (s1,b1)
                            g s = (s, Nothing)
                        write_obs system s
                        write_obs error_list []
                        modify_obs pr_obl $ \pos -> do
                            return $ M.unionWith f (pos `M.intersection` new_pos) (M.map g new_pos)
--                        swapMVar pos pos_list
--                        tryTakeMVar lbls
--                        putMVar lbls (Right $ keysSet pos_list)
--                        tryPutMVar tok ()
                        return ()
                    Left es   -> do
--                        tryTakeMVar lbls
--                        putMVar lbls (Left es)
                        write_obs error_list es
                        return ()

prover :: Shared -> IO ()
prover (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    req <- newEmptyMVar
    forM_ [1..8] $ \p -> forkOn p $ worker req 
    forever $ do
        takeMVar tok
        inc 200
        po <- read_obs pr_obl
--        renew po
--        po <- get
        forM_ (keys po) $ \k -> do
            po <- reads_obs pr_obl $ M.lookup k
            case po of
                Just (po,Nothing) -> do
                    liftIO $ putMVar req (k,po)
                _               -> return ()
--            update_state
        dec 200
    where
--        update_state = do
--            b <- liftIO $ isEmptyMVar tok
--            if b then return ()
--            else do
--                po <- liftIO $ readMVar pos
--                renew po
--                return ()
--        renew :: Map (Label,Label) Seq
--              -> StateT (Map (Label,Label) (Seq,Bool)) IO ()
--        renew pos = do
--            st <- get
--            put $ M.mapWithKey (f st) pos
--        f st k v = case M.lookup k st of
--            Just (po,r)
--                | v == po && not r -> (po,False)
--                | otherwise        -> (v, True)
--            Nothing -> (v,True)
        inc x = modify_obs working (return . (+x))
        dec x = modify_obs working (return . (+ (-x)))            
        worker req = forever $ do
            (k,po) <- takeMVar req
            inc 1
            r      <- discharge po
            dec 1
            modify_obs pr_obl $ return . insert k (po,Just $ r == Valid)
--            atomically $ writeTChan status (fst k,snd k,po,r == Valid)

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
            | otherwise = []

--collect :: Shared
--        -> IO ()
--collect (Shared { .. }) = do
--        tok <- newEmptyMVar
--        observe error_list tok
--        observe pr_obl tok
--        liftIO $ putStrLn "collect x"
--        forever $ do
--            liftIO $ threadDelay 500000
--            takeMVar tok
--            err <- gets errors
--            res <- gets result
--            merr <- gets error_msg
--            mpos <- gets failed_po
--            liftIO $ swapMVar merr $ map f err
--            liftIO $ swapMVar mpos $ concatMap g $ toList res
--            poll_result (Shared { .. })
--    where
--        f (x,i,j) = Ref fname x (i,j)
--        g ((x,y),(p,b))
--            | not b     = [Ref fname (show y) (1,1)]
--            | otherwise = []
            
--poll_result :: Shared
--            -> StateT Display IO () 
--poll_result (Shared { .. }) = do
--        wait $ do
--            liftIO $ threadDelay 500000
--            st <- take_n 10
--            ls <- liftIO $ tryTakeMVar lbls
--            case ls of
--                Just (Right ls) -> do 
--                    let f k _ = k `S.member` ls
--                    modify $ \d -> d
--                        { result = M.filterWithKey f $ result d 
--                        , labels = ls
--                        , errors = [] }
--                Just (Left es) ->
--                    modify $ \d -> d
--                        { errors = es }
--                Nothing -> return ()
--            lbls <- gets labels
--            forM_ st $ \(m,lbl,r,s) -> do
--                if (m,lbl) `S.member` lbls then
--                    modify $ \d -> d 
--                        { result = insert (m,lbl) (r,s) $ result d }
--                else return ()
--            return $ not (null st && isNothing ls)
--    where
--        take_n 0 = return []
--        take_n n = do
--            b <- liftIO $ atomically $ isEmptyTChan status
--            if b then
--                return []
--            else do
--                x  <- liftIO $ atomically $ readTChan status
--                xs <- take_n (n-1)
--                return (x:xs)

display :: Shared
        -> IO ()
display (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    observe error_list tok
    observe working tok
    liftIO $ clearScreen
    forever $ do
            takeMVar tok
            outs <- read_obs pr_obl
--            lbls <- read_obs labels
            es   <- read_obs error_list
            w    <- read_obs working
            liftIO $ do
--                tryTakeMVar ser
--                putMVar ser ((outs,lbls),es)
                -- xs <- forM (toList outs) $ \((m,lbl),(_,r)) -> do
                    -- if not r then
                        -- liftIO $ putMVar io $ format "{0}{1} - {2}" x m lbl
                        -- return [format " x {0} - {1}" m lbl]
                    -- else return []
                let ys = proof_report outs es (w /= 0)
                cursorUpLine $ length ys
                clearFromCursorToScreenBeginning
                forM_ ys $ \x -> do
                    -- clearLine
                    putStr x
                    clearFromCursorToLineEnd 
                    putStrLn ""
                putStrLn $ format "n workers: {0}" w
--        poll_result (Shared { .. })

serialize (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    forever $ do
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

summary (Shared { .. }) = do
        v <- newEmptyMVar
        observe system v
        forkIO $ forever $ do
            threadDelay 10000000
            takeMVar v
            s <- read_obs system
            produce_summaries s
        
keyboard = do
        xs <- getLine
        if map toLower xs == "quit" 
            then return ()
            else do
                putStrLn $ format "Invalid command: '{0}'" xs
                keyboard

data InterfaceStyle = 
        Terminal 
        | GUI ( MVar [Reference], MVar [Reference] )
    deriving Eq

run_pipeline fname = do
--        pos     <- newMVar M.empty
--        lbls    <- newEmptyMVar
--        tok     <- newEmptyMVar
--        ser     <- newEmptyMVar
--        status  <- newTChanIO
        system     <- new_obs empty_system
        working    <- new_obs 0
        error_list <- new_obs []
        exit_code  <- newEmptyMVar 
        m          <- load_pos fname M.empty
        pr_obl     <- new_obs m
        -- io      <- newEmptyMVar
--        working <- newMVar 0
        let sh = Shared { .. }
        forkIO $ do
            summary sh
            t1 <- forkIO $ prover sh -- (M.map f m)
            t2 <- forkIO $ serialize sh
            t3 <- forkIO $ parser sh
            t0 <- forkIO $ display sh 
    --                    (Display m s [] v0 v1)
            keyboard 
            putStrLn "received a 'quit' command"
            killThread t0
            killThread t1
            killThread t2
            killThread t3
        return sh

type Verifier = StablePtr (Shared)

run_verifier :: CString -> IO Verifier
run_verifier fname = do
    fname <- peekCString fname
    sh <- run_pipeline fname
    newStablePtr sh

--            merr <- gets error_msg
--            mpos <- gets failed_po
--            liftIO $ swapMVar mpos $ concatMap g $ toList res
--        g ((x,y),(p,b))
--            | not b     = [Ref fname (show y) (1,1)]
--            | otherwise = []

get_error_list :: Verifier -> IO CErrList
get_error_list v = do
        Shared { .. } <- deRefStablePtr v
        err <- read_obs error_list
        let xs = map (f fname) err
        r  <- newIORef (RL [] xs)
        newStablePtr r
    where
        f fname (x,i,j) = Ref fname x (i,j)

get_proof_obligations :: Verifier -> IO CErrList
get_proof_obligations v = do
        Shared { .. } <- deRefStablePtr v
        pos <- read_obs pr_obl
        let ys = concatMap (g fname) $ toList pos
        r  <- newIORef (RL [] ys)
        newStablePtr r
    where
        g fname ((_,y),(_,b))
            | b == Just False = [Ref fname (show y) (1,1)]
            | otherwise       = []
