module Interactive.Serialize where

    -- Modules
import Logic.Expr
import Logic.Proof

import UnitB.PO
import UnitB.Syntax

    -- Libraries
import Control.Lens hiding (Context)
import Control.Monad
import Control.Parallel.Strategies
import Control.Monad.State

import Data.ByteString.Builder
import           Data.Maybe
import           Data.Serialize as Ser ( Serialize(..) ) 
import           Data.Serialize.Put 
import           Data.Tuple
import qualified Data.HashMap.Strict as H

import GHC.Generics (Generic)

import System.Directory

import           Utilities.FileFormat
import           Utilities.Map as M 
        ( insert 
        , (!), fromList, toList
        , empty, mapKeys )
import qualified Utilities.Map as M 
import           Utilities.Table

instance Serialize Label where
instance Serialize Sort where
instance (Serialize n,Serialize t) => Serialize (AbsVar n t) where
instance Serialize Type where
instance Serialize (TypeCons Type) where
instance (Serialize n,Serialize t) => Serialize (AbsFun n t) where
instance (Serialize n,Serialize q,Serialize t) 
    => Serialize (AbsDef n t q) where
instance Serialize HOQuantifier where
instance Serialize QuantifierType where
instance Serialize QuantifierWD where
instance (Ord n,Serialize n,Serialize t,Serialize q) 
    => Serialize (GenContext n t q) where
instance (Serialize n,Serialize q,Serialize t,Serialize a)
    => Serialize (GenExpr n t a q) where
instance (Ord n,Serialize n,Serialize t,Serialize q,Serialize expr) 
    => Serialize (GenSequent n t q expr) where
instance Serialize SyntacticProp where
instance Serialize a => Serialize (ArgDep a) where
instance Serialize Rel where
instance Serialize Flipping where
instance Serialize Value where
instance Serialize MachineId where

{-# INLINABLE seqFileFormat #-}
seqFileFormat :: FileFormat (Table Key (Seq,Maybe Bool))
seqFileFormat = 
          failOnException 
        . compressedSequents ()
        . serializedLazy
        . compressed
        $ lazyByteStringFile

{-# INLINABLE compressedSequents #-}
compressedSequents :: err
                   -> FileFormat' err FileStruct
                   -> FileFormat' err (Table Key (Seq,Maybe Bool))
compressedSequents err = prismFormat' (const err) intSequentIso

{-# INLINABLE intSequentIso #-}
intSequentIso :: Iso' FileStruct (Table Key (Seq,Maybe Bool))
intSequentIso = iso iseq_to_seq seq_to_iseq

expr_number :: Expr -> ExprStore Int
expr_number expr = do
    n <- gets $ M.lookup expr
    case n of
        Just n  -> return n
        Nothing -> do
            n <- gets M.size
            modify $ insert expr n
            return n

decompress_seq :: SeqI -> ExprIndex Seq
decompress_seq = traverse (gets . flip (!))
            
compress_seq :: Seq -> ExprStore SeqI
compress_seq = traverse expr_number

decompress_map :: IntMap -> ExprIndex (Table Key (Seq,Maybe Bool))
decompress_map ms = do
        xs <- forM (uncurry zip ms) $ \(x,(j,z)) -> do
            y <- decompress_seq j
            return (x,(y,z))
        return $ fromList xs

compress_map :: Table Key (Seq,Maybe Bool) -> ExprStore IntMap    
compress_map m = do
        xs <- forM (toList m) $ \(x,(y,z)) -> do
            j <- compress_seq y
            return (x,(j,z))
        return $ unzip xs
        
type Seq    = Sequent
type SeqI   = GenSequent Name Type HOQuantifier Int
type Key    = (Label,Label)
-- type IntMap = [(Key,(SeqI,Bool))]
type IntMap = ([Key],[(SeqI,Maybe Bool)])
type ExprStore = State (H.HashMap Expr Int)
type ExprIndex = State (Table Int Expr)

load_pos :: FilePath 
         -> Table Key (Seq,Maybe Bool)
         -> IO (Table Key (Seq,Maybe Bool))
load_pos file pos = do
        let fname = file ++ ".state"
        b <- doesFileExist fname
        if b then do
            fromMaybe pos <$> readFormat seqFileFormat fname
        else return pos

data FileStruct = FileStruct IntMap (H.HashMap Expr Int) 
    deriving (Generic)

instance Serialize FileStruct where
    put (FileStruct (ks,seqs) ixs) = putBuilder $ 
            -- (parMconcat 10 xs)
            mconcat (xs  `using` parListChunk 10 rseq)
        where
            xs = builderOfList ks ++ builderOfList seqs ++ builderOfList (toList ixs)

parMconcat :: Monoid a => Int -> [a] -> a
parMconcat chunk xs = mconcat (xs `using` aux n)
    where
        n = length xs
        aux :: Monoid a => Int -> Strategy [a]
        aux sz xs | sz >= 2*chunk = (:[]).mconcat <$> parListSplitAt half (aux half) (aux $ sz - half) xs
                  | otherwise     = return [mconcat xs]
            where
                half = sz `div` 2


builderOfList :: Serialize a => [a] -> [Builder]
builderOfList xs = execPut (putWord64be (fromIntegral (length xs))) : map (execPut . Ser.put) xs

iseq_to_seq :: FileStruct
            -> Table Key (Seq,Maybe Bool)
iseq_to_seq (FileStruct x y) = evalState (decompress_map x) inv
    where
        inv = fromList $ map swap $ toList $ y
        
seq_to_iseq :: Table Key (Seq,Maybe Bool)
            -> FileStruct 
seq_to_iseq pos = FileStruct a b
    where
        (a,b) = runState (compress_map pos) empty
        
dump_pos :: FilePath -> Table Key (Seq,Maybe Bool) -> IO ()
dump_pos file pos = do 
        let fn     = file ++ ".state"
        writeFormat seqFileFormat fn pos

dump_z3 :: Maybe Label -> FilePath -> Table Key (Seq,Maybe Bool) -> IO ()
dump_z3 pat file pos = dump file (M.map fst 
        $ M.filterWithKey (const . matches) 
        $ mapKeys snd pos)
    where
        matches = maybe (const True) (==) pat

