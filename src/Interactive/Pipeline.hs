{-# LANGUAGE RecordWildCards #-}
module Interactive.Pipeline 
   ( run_pipeline, Params' (..), Params, pos )
where

    -- Modules
--import Browser
    
import Document.Document

import Documentation.SummaryGen

import Utilities.Config hiding ( wait )
import Interactive.Observable
import Interactive.Serialize 

import Logic.Expr

import UnitB.UnitB

import Z3.Z3 
        ( discharge
        , Validity ( .. ) )

    -- Libraries
import Control.DeepSeq
import Control.Concurrent
import Control.Concurrent.STM
import Control.Lens

import Control.Exception

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State
import Control.Precondition

import           Data.Char
import qualified Data.List as L
import           Data.Map as M 
                    ( insert, keys
                    , toList, unions )
import qualified Data.Map as M 

import GHC.Generics (Generic)

import System.Console.ANSI
import System.Directory
import System.Process

import Text.Printf.TH

import Utilities.Syntactic
import Utilities.TimeIt

    -- The pipeline is made of three processes:
    --  o the parser
    --  o the prover
    --  o the display
    --
    -- The prover and the parser _share_ a map of proof obligations
    -- The prover and the parser _share_ a list of PO labels
    -- The 
                
data Shared = Shared
        { working    :: Observable Int
        , system     :: Observable System
        , error_list :: Observable [Error]
        , pr_obl     :: Observable (M.Map Key (Seq,Maybe Bool))
        , fname      :: FilePath
        , exit_code  :: MVar ()
        , parser_state :: Observable ParserState
        , focus    :: Observable (Maybe String)
        , dump_cmd :: Observable (Maybe DumpCmd)
        , redraw   :: Observable Bool
        }

data ParserState = Idle Double | Parsing
    deriving Eq

type Params = Params' (M.Map Label (M.Map Label (Bool,Seq)))

data Params' pos = Params
        { path :: FilePath
        , verbose :: Bool
        , continuous :: Bool
        , no_dump :: Bool
        , no_verif :: Bool
        , reset :: Bool
        , _pos :: pos
        , init_focus :: Maybe String
        } deriving (Generic)

makeLenses ''Params'

instance NFData Params where

instance Show ParserState where
    show (Idle x) = [s|Idle %sms|] $ show $ round $ x * 1000
    show Parsing  = "Parsing"

parser :: Shared
       -> IO (IO ())
parser (Shared { .. })  = return $ do
        t <- getModificationTime fname
        write_obs parser_state Parsing
        (dt,()) <- timeItT $ parse
        write_obs parser_state (Idle dt)
        evalStateT (forever $ do
            liftIO $ do
                threadDelay 250000
            t0 <- get
            t1 <- liftIO $ getModificationTime fname
            if t0 == t1 then return ()
            else do
                put t1
                liftIO $ do
                    write_obs parser_state Parsing
                    (t,()) <- timeItT parse 
                    write_obs parser_state (Idle t)
            ) t
    where
        f m = return $ M.mapKeys (g $ _name m) $ proof_obligation m
            -- return $ fromList $ map (g $ _name m) $ toList $ x
        g lbl x = (lbl,x)
        h lbl (x,y) = ((lbl,x),y)
        parse = do
                xs <- liftIO $ runEitherT $ do
                    s  <- EitherT $ parse_system fname
                    ms <- hoistEither $ mapM f $ M.elems $ s!.machines
                    pos <- hoistEither $ mapM theory_po $ M.elems $ s!.theories
                    let cs = M.fromList $ map (uncurry h) $ do
                                (x,ys) <- zip (map label (s!.theories.to keys)) pos
                                y <- toList ys
                                return (x,y)
                    liftIO $ evaluate (ms, cs, s)
                case xs of
                    Right (ms,cs,s) -> do
                        let new_pos = unions (cs : map (M.mapKeys $ over _1 as_label) ms) :: M.Map Key Seq
                            f (s0,b0) (s1,b1)
                                | s0 == s1  = (s0,b0)
                                | otherwise = (s1,b1)
                            g s = (s, Nothing)
                        write_obs_fast system s
                        write_obs error_list []
                        modify_obs_fast pr_obl $ \pos -> do
                            evaluate $ M.unionWith f (pos `M.intersection` new_pos) (M.map g new_pos)
                        return ()
                    Left es   -> do
                        write_obs error_list es
                        return ()

prover :: Shared -> IO (IO ())
prover (Shared { .. }) = do
    tok <- newEmptyMVar
    observe pr_obl tok
    -- req <- newEmptyMVar
    req <- newTBQueueIO 20
    forM_ [1..40] $ \p -> forkOn p $ worker req 
    return $ forever $ do
        takeMVar tok
        inc 1
        po <- read_obs pr_obl
        forM_ (keys po) $ \k -> do
            po <- reads_obs pr_obl $ M.lookup k
            case po of
                Just (po,Nothing) -> do
                    liftIO $ atomically $ writeTBQueue req (k,po)
                    -- liftIO $ putMVar req (k,po)
                _               -> return ()
        dec 1
    where
        inc x = modify_obs working (return . (+x))
        dec x = modify_obs working (return . (+ (-x)))            
        -- handler :: 
        handler lbl@(_,x) (ErrorCall msg) = do
            write_obs dump_cmd $ Just $ Only x
            fail ([s|During %s: %s|] (pretty lbl) msg)
        worker req = forever $ do
            -- (k,po) <- takeMVar req
            (k,po) <- atomically $ readTBQueue req
            let k' = uncurry (</>) k
            inc 1
            r      <- catch (discharge k' po) (handler k)
            dec 1
            modify_obs pr_obl $ return . insert k (po,Just $ r == Valid)

proof_report :: Maybe String
             -> M.Map Key (Seq,Maybe Bool) 
             -> [Error] -> Bool 
             -> [String]
proof_report = proof_report' False

proof_report' :: Bool
              -> Maybe String
              -> M.Map Key (Seq,Maybe Bool) 
              -> [Error] -> Bool 
              -> [String]
proof_report' showSuccess pattern outs es isWorking = 
                     header ++
                     ys ++ 
                     ( if null es then []
                       else "> errors" : map report es ) ++
                     footer ++
                     [ if isWorking
                       then "> working ..."
                       else " "
                     ]
    where
        header  = maybe [] head pattern
        footer  = maybe [] foot pattern
        head pat = 
                [ "#"
                , "# Restricted to " ++ pat
                , "#"
                ]
        foot _ = 
                [ [s|# hidden: %d failures|] (length xs - length ys)
                ]
        xs = filter (failure . snd) (zip [0..] $ M.toAscList outs)
        ys = map f $ filter (match . snd) xs
        match xs  = maybe True (\f -> f `L.isInfixOf` map toLower (show $ snd $ fst xs)) pattern
        failure :: (a,(b,Maybe Bool)) -> Bool
        failure x
            | showSuccess = True
            | otherwise   = maybe False not $ snd $ snd x
        f (n,((m,lbl),(_,_))) = [s| x %s - %s  (%d)|] (pretty m) (pretty lbl) n

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
    observe focus tok
    observe redraw tok
    observe dump_cmd tok
    clearScreen
    return $ forever $ do
            outs <- read_obs pr_obl
            es   <- read_obs error_list
            w    <- read_obs working
            fil  <- read_obs focus
            let ys = proof_report fil outs es (w /= 0)
            cursorUpLine $ length ys
            clearFromCursorToScreenBeginning
            forM_ ys $ \x -> do
                let lns = lines x
                forM_ lns $ \x -> do
                    putStr x
                    clearFromCursorToLineEnd 
                    putStrLn ""
            let u = M.size $ M.filter (isNothing.snd) outs
            st <- read_obs parser_state
            du <- isJust `liftM` read_obs dump_cmd
            putStr $ [s|number of workers: %d; untried: %d; parser: %s; dumping: %s|] w u (show st) (show du)
            clearFromCursorToLineEnd 
            -- hFlush stdout
            putStrLn ""
            -- cursorDown 1
            -- putStr "-salut-"
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
        -- dump_pos fname pos
        writeFile 
            (fname ++ ".report") 
            (unlines $ proof_report' True Nothing out es False)

dump :: Shared -> IO (IO b)
dump (Shared { .. }) = do
    tok <- newEmptyMVar
    observe dump_cmd tok
    return $ forever $ do
        takeMVar tok
        pat <- read_obs dump_cmd 
        case pat of 
            Just pat -> do
                pos <- read_obs pr_obl
                dump_z3 pat fname pos
                write_obs dump_cmd Nothing
            Nothing -> return ()

pdfLatex :: Shared -> IO (IO ())
pdfLatex (Shared { .. }) = do
        v <- newEmptyMVar
        observe system v
        observe error_list v
        return $ forever $ do
            threadDelay 5000000
            takeMVar v
            readProcess "pdflatex" [fname] ""

summary :: Shared -> IO (IO ())
summary (Shared { .. }) = do
        v <- newEmptyMVar
        observe system v
        return $ forever $ do
            threadDelay 10000000
            takeMVar v
            s <- read_obs system
            produce_summaries fname s

keyboard :: Shared -> IO ()
keyboard sh@(Shared { .. }) = do
        modify_obs redraw $ return . not
        xs <- getLine
        let xs' = map toLower xs
            ws  = words xs'
        if xs' == "quit" 
        then return ()
        else do
            if xs' == "goto" then do
                xs <- read_obs error_list
                case xs of
                    (Error _ (LI fn i _)):_ -> do
                        open_at i fn
                    (MLError _ ((_,LI fn i _):|_)):_ -> do
                        open_at i fn
                    [] -> return ()
            else if xs' == "resetall" then do
                modify_obs pr_obl $ \m -> 
                    return $ M.map (\(x,_) -> (x,Nothing)) m
            else if xs' == "retry" then do
                let f (Just False) = Nothing
                    f x = x
                modify_obs pr_obl $ \m -> 
                    return $ m & traverse._2 %~ f
            else if xs' == "unfocus" then do
                write_obs focus Nothing
            else if take 1 ws == ["dump"]
                    && length ws == 2  
                    && all isDigit (ws ! 1) then do
                modify_obs dump_cmd $ \st -> do
                    if isNothing st then do
                        pos <- read_obs pr_obl
                        return $ Just $ Only $ snd $ keys pos ! (read $ ws ! 1)
                    else return Nothing
            else if xs == "dumpfail" then do
                modify_obs dump_cmd $ \st -> do
                    if isNothing st then
                        return $ Just AllFailed
                    else return st
            else if xs == "dumpall" then do
                modify_obs dump_cmd $ \st -> do
                    if isNothing st then
                        return $ Just All
                    else return st
            else if take 1 ws == ["focus"] && length ws == 2 then do
                write_obs focus $ Just (ws ! 1)
            else do
                putStrLn $ [s|Invalid command: '%s'|] xs
            keyboard sh

run_pipeline :: FilePath -> Params -> IO ()
run_pipeline fname (Params {..}) = do
        system     <- new_obs empty_system
        working    <- new_obs 0
        error_list <- new_obs []
        exit_code  <- newEmptyMVar 
        m          <- load_pos fname M.empty
        pr_obl     <- new_obs m
        parser_state <- new_obs (Idle 0)
        focus      <- new_obs init_focus
        dump_cmd   <- new_obs Nothing
        redraw     <- new_obs True
        setNumCapabilities 8
        let sh = Shared { .. }
        ts <- run_all $
            [ summary sh
            -- , prover sh -- (M.map f m)
            , serialize sh
            , parser sh
            , dump sh
            , display sh 
            , pdfLatex sh
            ] ++ 
            (guard (not no_verif) >> [prover sh])
        keyboard sh
        putStrLn "received a 'quit' command"
        mapM_ killThread ts
        pos <- read_obs pr_obl
        dump_pos fname pos
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
