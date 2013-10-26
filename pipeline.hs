{-# LANGUAGE RecordWildCards #-}
module Pipeline where

	-- Modules
import Document.Document

import UnitB.AST
import UnitB.PO

import Z3.Def
import Z3.Z3

	-- Libraries
import Control.Concurrent
-- import Control.Concurrent.MVar
-- import Control.Concurrent.Chan
import Control.Concurrent.STM.TChan

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.STM
-- import Control.Monad.Trans.Either
import Control.Monad.Trans.State

import Data.Map as M 
			( Map, empty, keysSet
			, insert, filterWithKey, keys
			, mapWithKey, lookup, fromList
			, toList, unions )
import Data.Maybe
import Data.Set as S 
			( Set, member, empty )

import System.Directory
import System.Console.ANSI

import Utilities.Format
import Utilities.Syntactic

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

data Shared = Shared
		{ pos     :: MVar (Map (Label,Label) Seq)
		, tok     :: MVar ()
		, lbls    :: MVar (Either [Error] (Set (Label,Label)))
		, status  :: TChan (Label,Label,Seq,Bool)
		, working :: MVar Int
		, io      :: MVar String
		}
			
data Display = Display
		{ result :: Map (Label,Label) (Seq,Bool)
		, labels :: Set (Label,Label)
		, errors :: [Error]
		}

console io = forever $ do
	xs <- takeMVar io
	putStrLn xs
			
parser :: String
	   -> Shared
	   -> IO ()
parser fn (Shared { .. })  = do
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
				let xs = ms >>= mapM f :: Either [Error] [Map (Label,Label) ProofObligation]
				case xs of
					Right ms -> do
						let pos_list = unions ms
						-- putMVar io $ format "Parser: Number of POs {0}" $ size pos_list
						swapMVar pos pos_list
						tryTakeMVar lbls
						putMVar lbls (Right $ keysSet pos_list)
						tryPutMVar tok ()
						return ()
					Left es   -> do
						tryTakeMVar lbls
						putMVar lbls (Left es)
						return ()
				-- putMVar io "done parsing"


prover :: Shared
	   -> StateT (Map (Label,Label) (Seq,Bool)) IO ()
prover (Shared { .. }) = forever $ do
		req <- liftIO $ newEmptyMVar
		liftIO $ do
			forM_ [1..8] $ const $ forkIO $ worker req
			takeMVar tok
			inc
		po <- liftIO $ readMVar pos
		renew po
		po <- get
		forM_ (keys po) $ \k -> do
			po <- gets $ M.lookup k
			case po of
				Just (po,True) -> do
					liftIO $ putMVar req (k,po)
					modify $ insert k (po,False)
				_			   -> return ()
			update_state
		liftIO $ dec
	where
		update_state = do
			b <- liftIO $ isEmptyMVar tok
			if b then return ()
			else do
				po <- liftIO $ readMVar pos
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
		inc = modifyMVar_ working (return . (+1))
		dec = modifyMVar_ working (return . (+ (-1)))			
		worker req = forever $ do
			(k,po) <- takeMVar req
			inc
			r      <- discharge po
			dec
			atomically $ writeTChan status (fst k,snd k,po,r == Valid)

	-- Note, the Set (Label,Label) should be part of the state.
display :: Shared
	    -> StateT Display IO ()
display (Shared { .. }) = forever $ do
		wait $ do
			-- liftIO $ putMVar io "Display: waiting"
			liftIO $ threadDelay 500000
			-- liftIO $ putMVar io "Display: reading channel"
			st <- take_n 10
			ls <- liftIO $ tryTakeMVar lbls
			case ls of
				Just (Right ls) -> do 
					let f k _ = k `S.member` ls
					modify $ \d -> d
						{ result = M.filterWithKey f $ result d 
						, labels = ls
						, errors = [] }
				Just (Left es) ->
					modify $ \d -> d
						{ errors = es }
				Nothing -> return ()
			lbls <- gets labels
			forM_ st $ \(m,lbl,r,s) -> do
				if (m,lbl) `S.member` lbls then
					modify $ \d -> d 
						{ result = insert (m,lbl) (r,s) $ result d }
				else return ()
			return $ not (null st && isNothing ls)
		out <- gets result
		es  <- gets errors
		-- liftIO $ forM_ [1 .. 30] $ const $ putStrLn ""
		xs <- forM (toList out) $ \((m,lbl),(_,r)) -> do
			let x = " xxx "
				-- | r 		= "  o  "
				-- | otherwise = " xxx "
			if not r then
				-- liftIO $ putMVar io $ format "{0}{1} - {2}" x m lbl
				return [format " x {1} - {2}" x m lbl]
			else return []
		b1 <- liftIO $ readMVar working
		b2 <- liftIO $ atomically $ isEmptyTChan status
		let ys = concat xs ++ 
				 ( if null es then []
				   else "> errors" : map report es ) ++
				 [ if b1 == 0 && b2
					then ""
					else "> working ..."
				 ] 
		-- liftIO $ clearScreen
		liftIO $ cursorUpLine $ length ys
		liftIO $ do
			clearFromCursorToScreenBeginning
			forM_ ys $ \x -> do
				clearLine
				putStrLn x
		-- liftIO $ putStrLn $ unlines ys
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
	pos     <- newMVar M.empty
	lbls    <- newEmptyMVar
	tok     <- newEmptyMVar
	status  <- newTChanIO
	io      <- newEmptyMVar
	working <- newMVar 0
	let sh = Shared { .. }
	forkIO $ evalStateT (display sh) (Display M.empty S.empty [])
	forkIO $ evalStateT (prover sh) M.empty
	forkIO $ console io
	parser fn sh
