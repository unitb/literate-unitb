module Serialize where

	-- Modules
import UnitB.AST
-- import UnitB.PO

import Z3.Def

	-- Libraries
import Control.Monad
import Control.Monad.State

import qualified Data.ByteString as BS
import Data.Map as M 
		( Map, lookup, size, insert 
		, (!), fromList, toList
		, empty)
import Data.Serialize ( Serialize, encode, decode )
import Data.Set as S ( Set )
import Data.Tuple

import System.Directory

instance Serialize Label where
instance Serialize Sort where
instance Serialize Var where
instance Serialize Type where
instance Serialize Fun where
instance Serialize Def where
instance Serialize Quantifier where
instance Serialize Context where
instance Serialize Expr where
instance Serialize ProofObligation where

expr_number :: Expr -> State (Map Expr Int) Int
expr_number expr = do
	n <- gets $ M.lookup expr
	case n of
		Just n  -> return n
		Nothing -> do
			n <- gets M.size
			modify $ insert expr n
			return n

decompress_seq :: SeqI -> ExprIndex Seq
decompress_seq (ctx,hs,b,g') = do
		hyps <- forM hs $ \x -> gets (! x)
		g    <- gets (! g')
		return (ProofObligation ctx hyps b g)
			
compress_seq :: Seq -> ExprStore SeqI
compress_seq (ProofObligation ctx hyps b g) = do
		hs <- forM hyps expr_number
		g' <- expr_number g
		return (ctx,hs,b,g')

decompress_map :: IntMap -> ExprIndex (Map Key (Seq,Bool))
decompress_map ms = do
		xs <- forM ms $ \(x,(j,z)) -> do
			y <- decompress_seq j
			return (x,(y,z))
		return $ fromList xs

compress_map :: Map Key (Seq,Bool) -> ExprStore IntMap	
compress_map m = do
		forM (toList m) $ \(x,(y,z)) -> do
			j <- compress_seq y
			return (x,(j,z))
		
type Seq    = ProofObligation
type SeqI   = (Context,[Int],Bool,Int)
type Key    = (Label,Label)
type IntMap = [(Key,(SeqI,Bool))]
type ExprStore = State (Map Expr Int)
type ExprIndex = State (Map Int Expr)

load_pos :: FilePath 
		 -> (Map Key (Seq,Bool), Set Key)
		 -> IO (Map Key (Seq,Bool), Set Key)
load_pos file pos = do
        b <- doesFileExist file
        if b then do
            xs <- BS.readFile $ file ++ ".state"
            either 
                (const $ return pos) 
                f $ decode xs
        else return pos

f :: ((IntMap,Map Expr Int),Set Key) 
  -> IO (Map Key (Seq,Bool), Set Key)
f ((x,y),z) = return (evalState (decompress_map x) inv,z)
	where
		inv = fromList $ map swap $ toList $ y
		
-- load_pos


		
-- dump_pos :: Serialize a => FilePath -> a -> IO ()
dump_pos file (pos,x) = do
        let fn     = file ++ ".state"
            new_po = (runState (compress_map pos) empty,x)
        BS.writeFile fn $ encode new_po