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
import Control.Applicative
import Control.CoApplicative
import Control.Concurrent
import Control.Concurrent.Async.Priority
import Control.Concurrent.STM
import Control.DeepSeq
import Control.Lens
import Control.Lens.Extras

import Control.Exception

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Either
import Control.Monad.Trans.State
import Control.Precondition

import           Data.Char
import qualified Data.List as L
import           Data.Map.Class as M 
                    ( keys
                    , toList )
import qualified Data.Map.Class as M 
import           Data.Map.These as M
import           Data.PartialOrd

import GHC.Generics (Generic)

import System.Console.ANSI
import System.Directory

import Text.Printf.TH

import Utilities.Syntactic
import Utilities.Table
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
        { system     :: Observable System
        , error_list :: Observable [Error]
        , pr_in      :: Observable (Table Key Seq)
        , pr_obl     :: Observable (Table Key (Seq,ProofState))
        , fname      :: FilePath
        , exit_code  :: MVar ()
        , parser_state :: Observable ParserState
        , focus    :: Observable (Maybe String)
        , dump_cmd :: Observable (Maybe (Maybe Label))
        , redraw   :: Observable Bool
        }

data ProofState = Untried | Tried Bool | Sparked
    deriving (Show,Eq)

data ParserState = Idle Double | Parsing
    deriving Eq

type Params = Params' (Table Label (Table Label (Bool,Seq)))

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
makePrisms ''ProofState

instance NFData Params where

instance Show ParserState where
    show (Idle x) = [printf|Idle %dms|] $ round $ x * 1000
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
                    (t,()) <- timeItT $ parse 
                    write_obs parser_state (Idle t)
            ) t
    where
        f m = return $ M.mapKeys (g $ _name m) $ proof_obligation m
            -- return $ fromList $ map (g $ _name m) $ toList $ x
        g lbl x = (lbl,x)
        h lbl (x,y) = ((lbl,x),y)
        parse = do
                xs <- liftIO $ timeIt $ runEitherT $ do
                    s  <- EitherT $ parse_system fname
                    ms <- hoistEither $ mapM f $ M.ascElems $ s!.machines
                    pos <- hoistEither $ mapM theory_po $ M.ascElems $ s!.theories
                    let cs = M.fromList $ map (uncurry h) $ do
                                (x,ys) <- zip (map label (s!.theories.to keys)) pos
                                y <- toList ys
                                return (x,y)
                    liftIO $ evaluate (ms, cs, s)
                timeIt $ case xs of
                    Right (ms,cs,s) -> do
                        let 
                            ms' = map (M.mapKeys $ over _1 as_label) ms
                        write_obs_fast system s
                        write_obs error_list []
                        write_obs_fast pr_in $ M.unions (cs:ms')
                        return ()
                    Left es   -> do
                        write_obs error_list es
                        return ()

type ProverState s = (Table Key (Seq, Bool),Table Key (Seq, Async s Bool))

prover :: Shared -> IO (IO ())
prover (Shared { .. }) = do
    return $ withScheduler 2 $ do
        tasks <- liftIO $ newTVarIO (M.empty,M.empty)
        concurrently (spark tasks) (gather tasks)
        return ()
    where
        spark :: TVar (ProverState s) -> Sched s ()
        spark s = do
            tok <- lift newEmptyTMVarIO
            lift $ observe pr_obl tok
            forever $ do
                ((m0,m1),po) <- lift $ atomically $ do
                    takeTMVar tok
                    liftA2 (,) 
                        (readTVar s)
                        (read_obs_STM pr_in)
                m <- fmap (M.mapEither (view distr) . M.mapMaybe id)
                    $ mapConcurrently id
                    $ mapOnUnionWithKey update po (
                            (m0 & traverse._2 %~ Left) 
                    `M.union` (m1 & traverse._2 %~ Right)) 
                lift $ atomically $ do
                    writeTVar s m
        gather :: TVar (ProverState s) -> Sched s ()
        gather s = forever $ do
            atomically' $ do
                (_,m) <- lift $ readTVar s
                (m0,m1) <- M.mapEither (view distr) 
                    <$> (traverse._2) (unfail' waitSTM) m
                guard $ not $ M.null m1
                lift $ do
                    modifyTVar s $ (_1 %~ M.union m1) . (_2 .~ m0)
                    (res,task) <- readTVar s
                    write_obs_fast_STM pr_obl $
                                    (res  & traverse._2 %~ Tried)
                        `M.union`   (task & traverse._2 .~ Untried)

update :: Key
       -> These Seq (Seq, Either Bool (Async s Bool))
       -> Sched s (Maybe (Seq, Either Bool (Async s Bool)))
update lbl (This s)    = Just . (s,) . Right <$> startProver High lbl s
update _   (That s)    = Nothing <$ maybe 
                                (return ()) 
                                cancel 
                                (rightToMaybe $ snd s)
update lbl (These s' (s,r)) = 
        case cmp of
            Comp EQ -> return $ Just (s',r)
            _ -> do
                either (const $ return ()) cancel r
                Just . (s',) . Right <$> startProver p lbl s'
    where
        cmp = partCompare s' s
        p = case (r,cmp) of
                (Left _,Comp GT) -> Low
                _           -> High

startProver :: Priority -> Key -> Seq 
            -> Sched s (Async s Bool)
startProver p lbl s = async p $ (Valid ==) 
                <$> discharge (uncurry (</>) lbl) s

proof_report :: Maybe String
             -> Table Key (Seq,ProofState) 
             -> [Error] -> Bool 
             -> [String]
proof_report pattern outs es b = 
                     header ++
                     ys ++ 
                     ( if null es then []
                       else "> errors" : map report es ) ++
                     footer ++
                     [ if b
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
                [ [printf|# hidden: %d failures|] (length xs - length ys)
                ]
        xs = filter (failure . snd) (zip [0..] $ M.toAscList outs)
        ys = map f $ filter (match . snd) xs
        match xs  = maybe True (\f -> f `L.isInfixOf` map toLower (show $ snd $ fst xs)) pattern
        failure :: (a, (b, ProofState)) -> Bool
        failure = maybe False not . preview _Tried . snd . snd
        f (n,((m,lbl),(_,_))) = [printf| x %s - %s  (%d)|] (pretty m) (pretty lbl) n

run_all :: [IO (IO ())] -> IO [ThreadId]
run_all xs = do
        ys <- sequence xs
        mapM f ys
    where
        f cmd = forkIO $ cmd

display :: Shared
        -> IO (IO ())
display (Shared { .. }) = do
    tok <- newEmptyTMVarIO
    observe pr_obl tok
    observe error_list tok
    observe parser_state tok
    observe focus tok
    observe redraw tok
    observe dump_cmd tok
    clearScreen
    return $ forever $ do
            outs <- read_obs pr_obl
            es   <- read_obs error_list
            fil  <- read_obs focus
            let w  = M.size $ M.filter (is _Tried.snd) outs 
                ys = proof_report fil outs es (w /= 0)
            cursorUpLine $ length ys
            clearFromCursorToScreenBeginning
            forM_ ys $ \x -> do
                let lns = lines x
                forM_ lns $ \x -> do
                    putStr x
                    clearFromCursorToLineEnd 
                    putStrLn ""
            let u = M.size $ M.filter (isn't _Tried.snd) outs
            st <- read_obs parser_state
            du <- isJust `liftM` read_obs dump_cmd
            putStr $ [printf|done: %d; untried: %d; parser: %s; dumping: %s|] 
                        w u (show st) (show du)
            clearFromCursorToLineEnd 
            -- hFlush stdout
            putStrLn ""
            -- cursorDown 1
            -- putStr "-salut-"
            threadDelay 500000
            atomically $ takeTMVar tok

serialize :: Shared -> IO (IO ())
serialize (Shared { .. }) = do
    tok <- newEmptyTMVarIO
    observe pr_obl tok
    return $ forever $ do
        threadDelay 10000000
        atomically $ takeTMVar tok
        pos <- read_obs pr_obl
        let out = pos
--        (pos@(out,_),es) <- takeMVar ser
        es <- read_obs error_list
        -- dump_pos fname pos
        writeFile 
            (fname ++ ".report") 
            (unlines $ proof_report Nothing out es False)

dump :: Shared -> IO (IO b)
dump (Shared { .. }) = do
    tok <- newEmptyTMVarIO
    observe dump_cmd tok
    return $ forever $ do
        atomically $ takeTMVar tok
        pat <- read_obs dump_cmd 
        case pat of 
            Just pat -> do
                pos <- read_obs pr_obl
                dump_z3 pat fname (pos & traverse._2 %~ preview _Tried)
                write_obs dump_cmd Nothing
            Nothing -> return ()

summary :: Shared -> IO (IO ())
summary (Shared { .. }) = do
        v <- newEmptyTMVarIO
        observe system v
        return $ forever $ do
            threadDelay 10000000
            atomically $ takeTMVar v
            s <- read_obs system
            produce_summaries fname s

keyboard :: Shared -> IO ()
keyboard sh@(Shared { .. }) = do
        modify_obs' redraw not
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
                    (MLError _ ((_,LI fn i _):_)):_ -> do
                        open_at i fn
                    (MLError _ []):_ -> return ()
                    [] -> return ()
            else if xs' == "reset" then do
                modify_obs' pr_obl $ \m -> 
                    M.map (\(x,_) -> (x,Untried)) m
            else if xs' == "unfocus" then do
                write_obs focus Nothing
            else if take 1 ws == ["dump"]
                    && length ws == 2  
                    && all isDigit (ws ! 1) then do
                atomically $ modify_obs_STM dump_cmd $ \st -> do
                    if isNothing st then do
                        pos <- read_obs_STM pr_obl
                        return $ Just $ Just $ snd $ keys pos ! (read $ ws ! 1)
                    else return Nothing
            else if xs == "dumpall" then do
                atomically $ modify_obs_STM dump_cmd $ \st -> do
                    if isNothing st then
                        return $ Just Nothing
                    else return st
            else if take 1 ws == ["focus"] && length ws == 2 then do
                write_obs focus $ Just (ws ! 1)
            else do
                putStrLn $ [printf|Invalid command: '%s'|] xs
            keyboard sh

run_pipeline :: FilePath -> Params -> IO ()
run_pipeline fname (Params {..}) = do
        system     <- new_obs empty_system
        error_list <- new_obs []
        exit_code  <- newEmptyMVar 
        m          <- load_pos fname M.empty
        pr_in      <- new_obs M.empty
        pr_obl     <- new_obs (m & traverse._2 %~ maybe Untried Tried)
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
            ] ++ 
            (guard (not no_verif) >> [prover sh])
        keyboard sh
        putStrLn "received a 'quit' command"
        mapM_ killThread ts
        pos <- read_obs pr_obl
        dump_pos fname (pos & traverse._2 %~ preview _Tried)
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
