module Interactive.Serialize where

    -- Modules
import Logic.Expr
import Logic.Proof

import UnitB.PO

    -- Libraries
import Codec.Compression.Zlib

import Control.Exception    
import Control.Monad
import Control.Monad.State

import           Data.ByteString.Lazy as BS
        ( writeFile, readFile )
import           Data.ByteString.Lazy (toStrict,fromStrict)
import           Data.Map as M 
        ( Map, insert 
        , (!), fromList, toList
        , empty, mapKeys )
import qualified Data.Map as M 
import           Data.Serialize ( Serialize, encode, decode )
import           Data.Tuple

import System.Directory

instance Serialize Label where
instance Serialize Sort where
instance Serialize Var where
instance Serialize Type where
instance Serialize (TypeCons Type) where
instance Serialize Fun where
instance Serialize Def where
instance Serialize HOQuantifier where
instance Serialize QuantifierType where
instance Serialize QuantifierWD where
instance Serialize Context where
instance Serialize Expr where
instance Serialize Sequent where
instance Serialize SyntacticProp where
instance Serialize a => Serialize (ArgDep a) where
instance Serialize Rel where
instance Serialize Flipping where
instance Serialize Value where

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
decompress_seq (ctx,m,as,hs,g') = do
        hyps <- forM hs $ \(x,y) -> do
                    y <- gets (! y)
                    return (x,y)
        asm  <- forM as $ \x -> gets (! x)
        g    <- gets (! g')
        return (Sequent ctx m asm (fromList hyps) g)
            
compress_seq :: Seq -> ExprStore SeqI
compress_seq (Sequent ctx m asm hyps g) = do
        as <- forM asm  expr_number
        hs <- forM (M.elems hyps) expr_number
        g' <- expr_number g
        return (ctx,m,as,zip (M.keys hyps) hs,g')

decompress_map :: IntMap -> ExprIndex (Map Key (Seq,Maybe Bool))
decompress_map ms = do
        xs <- forM (uncurry zip ms) $ \(x,(j,z)) -> do
            y <- decompress_seq j
            return (x,(y,z))
        return $ fromList xs

compress_map :: Map Key (Seq,Maybe Bool) -> ExprStore IntMap    
compress_map m = do
        xs <- forM (toList m) $ \(x,(y,z)) -> do
            j <- compress_seq y
            return (x,(j,z))
        return $ unzip xs
        
type Seq    = Sequent
type SeqI   = (Context,SyntacticProp,[Int],[(Label,Int)],Int)
type Key    = (Label,Label)
-- type IntMap = [(Key,(SeqI,Bool))]
type IntMap = ([Key],[(SeqI,Maybe Bool)])
type ExprStore = State (Map Expr Int)
type ExprIndex = State (Map Int Expr)

load_pos :: FilePath 
         -> Map Key (Seq,Maybe Bool)
         -> IO (Map Key (Seq,Maybe Bool))
load_pos file pos = do
        let fname = file ++ ".state"
        b <- doesFileExist fname
        let handler :: SomeException -> IO (Map Key (Seq,Maybe Bool))
            handler _ = return pos
        if b then do
            xs <- BS.readFile $ fname
            catch (do
                either 
                    (const $ return pos) 
                    (evaluate . iseq_to_seq)
                    $ decode $ toStrict $ decompress xs)
                handler

        else return pos

type FileStruct = (IntMap,Map Expr Int) 
        
iseq_to_seq :: FileStruct
            -> Map Key (Seq,Maybe Bool)
iseq_to_seq (x,y) = evalState (decompress_map x) inv
    where
        inv = fromList $ map swap $ toList $ y
        
seq_to_iseq :: Map Key (Seq,Maybe Bool)
            -> FileStruct 
seq_to_iseq pos = (a,b)
    where
        (a,b) = runState (compress_map pos) empty
        
dump_pos :: FilePath -> Map Key (Seq,Maybe Bool) -> IO ()
dump_pos file pos = do 
        let fn     = file ++ ".state"
            new_po = seq_to_iseq pos
        BS.writeFile fn $ compress $ fromStrict $ encode new_po

dump_z3 :: Maybe Label -> FilePath -> Map Key (Seq,Maybe Bool) -> IO ()
dump_z3 pat file pos = dump file (M.map fst 
        $ M.filterWithKey (const . matches) 
        $ mapKeys snd pos)
    where
        matches = maybe (const True) (==) pat

