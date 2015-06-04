module Document.Tests.Suite where

    -- Modules
import Document.Document as Doc

import Logic.Expr as E
import Logic.Proof

import UnitB.AST
import UnitB.PO as PO

import Z3.Z3

    -- Libraries
import Control.Applicative ((<$>))
import Control.Arrow hiding (right,left)
import Control.Concurrent
import Control.Exception
import Control.Lens

import Control.Monad.Trans
import Control.Monad.Trans.Either

import Data.Either.Combinators
import Data.List as L
import Data.List.Utils as L
import Data.Map as M
import Data.Time

import Utilities.Format
import Utilities.Syntactic

import System.Directory
import System.IO.Unsafe

type POResult = (String,Map Label Sequent)
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
                ms = machines <$> sys >>= traverseWithKey (cmd PO.proof_obligation)
                ts = theories <$> sys >>= traverseWithKey (cmd theory_po)
            putMVar pos $ M.insert path ((ms,ts),t) m
            return (ms,ts)

verify :: FilePath -> Int -> IO POResult
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

stripAnnotation :: Expr -> Expr
stripAnnotation e = E.rewrite stripAnnotation $ f e
    where
        strip = set annotation [] 
        f (FunApp fun xs) = FunApp (strip fun) xs
        f e = e

proof_obligation_stripped :: FilePath -> String -> Int -> IO String
proof_obligation_stripped = proof_obligation_with stripAnnotation

proof_obligation :: FilePath -> String -> Int -> IO String
proof_obligation = proof_obligation_with id

sequent :: FilePath -> String 
        -> Int -> IO (Either String Sequent)
sequent path lbl i = runEitherT $ do
        xs <- EitherT $ (mapLeft show_err . fst) 
            <$> list_file_obligations' path
        if i < size xs then do
            let pos = snd $ snd $ i `elemAt` xs
            case label lbl `M.lookup` pos of
                Just po -> 
                    return po
                Nothing ->
                    left $ format "invalid label: {0}\n{1}" lbl $ 
                        unlines $ L.map show $ keys pos
        else
            left $ format "accessing {0}th refinement out of {1}" i (size xs)   

proof_obligation_with :: (Expr -> Expr) 
                      -> FilePath -> String 
                      -> Int -> IO String
proof_obligation_with f path lbl i = either id disp <$> sequent path lbl i
    where
        disp po = format "; {0}\n{1}; {2}\n" lbl (cmd po) lbl
        cmd po = unlines $ L.map pretty_print' 
                                  $ z3_code 
                                  $ po & nameless %~ L.map f
                                       & named %~ M.map f
                                       & goal %~ f

find_errors :: FilePath -> IO String 
find_errors path = do
    p <- canonicalizePath path
    m <- fst <$> list_file_obligations' path
    return $ either 
        (L.replace (p ++ ":") "error " . unlines . L.map report) 
        (const $ "no errors")
        m

parse_machine :: FilePath -> Int -> IO (Either [Error] Machine)
parse_machine path n = fmap (!! n) <$> parse path

parse :: FilePath -> IO (Either [Error] [Machine])
parse path = do
    (fmap (elems . M.map fst) . fst) <$> list_file_obligations' path

verify_thy :: FilePath -> String -> IO POResult
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

