module Pipeline where

	-- Modules
import Document.Document

import UnitB.AST
import UnitB.Label
import UnitB.PO

import Z3.Def
import Z3.Z3

	-- Libraries
import Control.Concurrent
import Control.Concurrent.MVar
-- import Control.Concurrent.Chan
import Control.Concurrent.STM.TChan

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.STM
import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import Data.Map as M 
			( Map, empty, alter, filter
			, insert, filterWithKey, keys
			, mapWithKey, lookup, fromList
			, toList, unions, size )
import Data.Maybe
import Data.Set as S ( Set, member )

import System.Directory

import Utilities.Format

	-- The pipeline is made of three processes:
	--	o the parser
	--  o the prover
	--  o the display
	--
	-- The prover and the parser _share_ a map of proof obligations
	-- The prover and the parser _share_ a list of PO labels
	-- The 

type Seq = ProofObligation
	
default_po_state = False

wait :: Monad m => m Bool -> m ()
wait m = do
		b <- m
		if b 
			then return ()
			else wait m

data Display = Display
			
console io = forever $ do
	xs <- takeMVar io
	putStrLn xs
			
parser :: String
	   -> MVar (Map (Label,Label) Seq) 
	   -> MVar ()
	   -> MVar (Set (Label,Label))
	   -> MVar String
	   -> IO ()
parser fn pos tok lbls io  = do
		-- putMVar io "started"
		t <- getModificationTime fn
		parse
		evalStateT (forever $ do
			liftIO $ threadDelay 1000000
			t0 <- get
			t1 <- liftIO $ getModificationTime fn
			if t0 == t1 then return ()
			else do
				put t1
				liftIO $ parse
			) t
	where
		f m = do
			x <- proof_obligation m
			return $ fromList $ map (g $ _name m) $ toList $ x
		g lbl (x,y) = ((lbl,x),y)
		parse = do
				-- putMVar io "parsing"
				ms <- parse_machine fn
				let xs = ms >>= mapM f
				case xs of
					Right ms -> do
						let pos_list = unions ms
						-- putMVar io $ format "Parser: Number of POs {0}" $ size pos_list
						swapMVar pos pos_list
						tryPutMVar tok ()
						return ()
					Left _   -> return ()
				-- putMVar io "done parsing"


prover :: MVar (Map (Label,Label) Seq) 
	   -> MVar ()
	   -> TChan (Label,Label,Seq,Bool)
	   -> MVar ()
	   -> MVar String
	   -> StateT (Map (Label,Label) (Seq,Bool)) IO ()
prover pos tok status working io = forever $ do
		req <- liftIO $ newEmptyMVar
		liftIO $ forM_ [1..8] $ const $ forkIO $ worker req
		liftIO $ do
			-- putMVar io "Prover: waiting"
			takeMVar working
			takeMVar tok
			putMVar working ()
			-- putMVar io "Prover: got a token"
		po <- liftIO $ readMVar pos
		renew po
		po <- get
		-- liftIO $ putMVar io $ format "Prover: Number of POs {0}" $ size po
		forM_ (keys po) $ \k -> do
			po <- gets $ M.lookup k
			case po of
				Just (po,True) -> do
					-- liftIO $ putMVar io "proving"
					-- r <- liftIO $ discharge po
					liftIO $ putMVar req (k,po)
					modify $ insert k (po,False)
					-- liftIO $ atomically $ writeTChan status (fst k,snd k,po,r == Valid)
				_			   -> return ()
			update_state
	where
		update_state = do
			b <- liftIO $ isEmptyMVar tok
			if b then return ()
			else do
				po <- liftIO $ readMVar pos
				-- liftIO $ putMVar io $ format "Prover: received POs {0}" $ size po
				renew po
				return ()
		renew :: Map (Label,Label) Seq
			  -> StateT (Map (Label,Label) (Seq,Bool)) IO ()
		renew pos = do
			st <- get
			put $ M.mapWithKey (f st) pos
		f st k v = case M.lookup k st of
			Just (po,r)
				| v == po && not r -> (po,False)
				| otherwise        -> (v, True)
			Nothing -> (v,True)
		worker req = forever $ do
			(k,po) <- takeMVar req
			r      <- discharge po
			atomically $ writeTChan status (fst k,snd k,po,r == Valid)

	-- Note, the Set (Label,Label) should be part of the state.
display :: TChan (Label,Label,Seq,Bool)
	    -> MVar (Set (Label,Label))
		-> MVar ()
		-> MVar String
	    -> StateT (Map (Label,Label) (Seq, Bool)) IO ()
display status lbls working io = forever $ do
		wait $ do
			-- liftIO $ putMVar io "Display: waiting"
			liftIO $ threadDelay 1000000
			-- liftIO $ putMVar io "Display: reading channel"
			st <- take_n 10
			ls <- liftIO $ tryTakeMVar lbls
			forM_ st $ \(m,lbl,r,s) -> do
				modify $ insert (m,lbl) (r,s)
			case ls of
				Just ls ->
					modify $ M.filterWithKey (\k _ -> k `S.member` ls)
				Nothing -> return ()
			return $ not $ null st && isNothing ls
		out <- get
		liftIO $ forM_ [1 .. 30] $ const $ putStrLn ""
		xs <- forM (toList out) $ \((m,lbl),(s,r)) -> do
			let x = " xxx "
				-- | r 		= "  o  "
				-- | otherwise = " xxx "
			if not r then
				-- liftIO $ putMVar io $ format "{0}{1} - {2}" x m lbl
				return [format "{0}{1} - {2}" x m lbl]
			else return []
		liftIO $ putStrLn $ unlines $ concat xs
		b <- liftIO $ isEmptyMVar working
		liftIO $ if b 
			then putStrLn ""
			else putStrLn "> working ..."
	where
		take_n 0 = return []
		take_n n = do
			b <- liftIO $ atomically $ isEmptyTChan status
			if b then
				return []
			else do
				-- liftIO $ putMVar io "receiving POs"
				x  <- liftIO $ atomically $ readTChan status
				xs <- take_n (n-1)
				return (x:xs)

run_pipeline fn = do
	pos     <- newMVar empty
	lbls    <- newEmptyMVar
	tok     <- newEmptyMVar
	status  <- newTChanIO
	io      <- newEmptyMVar
	working <- newMVar ()
	forkIO $ evalStateT (display status lbls working io) M.empty
	forkIO $ evalStateT (prover pos tok status working io) M.empty
	forkIO $ console io
	parser fn pos tok lbls io
