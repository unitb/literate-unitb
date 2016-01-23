module Document.Tests.Suite 
    ( module Document.Tests.Suite 
    , module Control.Monad.Trans.Either 
    , module UnitB.UnitB
    , Error(..) )
where

    -- Modules
import Document.Document as Doc

import Logic.Expr as E
import Logic.Proof

import UnitB.PO
import UnitB.UnitB hiding (proof_obligation,raw_proof_obligation)
import qualified UnitB.UnitB as UB

import Z3.Z3

    -- Libraries
import Control.Arrow hiding (right,left)
import Control.Concurrent
import Control.Exception
import Control.Lens

import Control.Monad.Trans
import Control.Monad.Trans.Either

import Data.Either.Combinators
import Data.List as L hiding (lookup)
import Data.List.Utils as L
import Data.Time

import GHC.Stack

import Prelude hiding (lookup)
import PseudoMacros

import Utilities.Format
import Utilities.Map as M hiding (lookup)
import Utilities.Syntactic
import Utilities.Table

import System.Directory
import System.IO.Unsafe

type POResult = (String,Table Label Sequent)
type POS sid a = Either [Error] (Table sid (a, Table Label Sequent))

hide_error_path :: Bool
hide_error_path = True

pos :: MVar (Map FilePath ((POS MachineId Machine,POS String Theory), UTCTime))
pos = unsafePerformIO $ newMVar M.empty

list_file_obligations' :: FilePath -> IO (POS MachineId Machine,POS String Theory)
list_file_obligations' path = do
    path <- canonicalizePath path
    t <- getModificationTime path
    m <- takeMVar pos
    sys <- parse_system path
    let cmd :: Monad m => (b -> m c) -> b -> m (b,c)
        cmd f = runKleisli (Kleisli return &&& Kleisli f)
        -- ms :: Either 
        ms = M.map (id &&& UB.proof_obligation).view' machines <$> sys 
            -- >>= traverseWithKey (cmd PO.proof_obligation)
        ts = view' theories <$> sys >>= traverse (cmd theory_po)
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

all_proof_obligations' :: FilePath -> EitherT String IO [Table Label String]
all_proof_obligations' path = do
        xs <- bimapEitherT show id
            $ EitherT $ fst <$> list_file_obligations' path
        let pos = M.ascElems $ M.map snd xs
            cmd = L.map (M.map $ unlines . L.map pretty_print' . z3_code) pos
        return cmd

all_proof_obligations :: FilePath -> IO (Either String [Table Label String])
all_proof_obligations = runEitherT . all_proof_obligations'

withLI :: (?loc :: CallStack) => Either String a -> Either [Error] a
withLI = mapLeft $ errorTrace [] ?loc

withLI' :: (?loc :: CallStack,Monad m) => EitherT String m a -> EitherT [Error] m a
withLI' (EitherT cmd) = EitherT $ withLI <$> cmd

raw_proof_obligation :: FilePath -> String -> Int -> IO String
raw_proof_obligation path lbl i = makeReport $ do
        ms <- EitherT $ Doc.parse_machine path
        m  <- Document.Tests.Suite.lookup i ms
        po <- hoistEither $ withLI $ lookupSequent 
                (label lbl) 
                (UB.raw_proof_obligation m)
        let cmd = unlines $ L.map pretty_print' $ z3_code po
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

lookupSequent :: Label -> Table Label Sequent -> Either String Sequent
lookupSequent lbl pos = case pos^?ix lbl of
                Just po -> 
                    Right po
                Nothing ->
                    Left $ format "invalid label: {0}\n{1}" lbl $ 
                        unlines $ L.map show $ keys pos

lookupSequent' :: Monad m 
               => Label -> Table Label Sequent 
               -> EitherT String m Sequent
lookupSequent' lbl m = hoistEither $ lookupSequent lbl m

sequent :: FilePath -> String 
        -> Int -> IO (Either String Sequent)
sequent path lbl i = runEitherT $ sequent' path lbl i

sequent' :: FilePath -> String 
         -> Int -> EitherT String IO Sequent
sequent' path lbl i = do
        xs <- EitherT $ (mapLeft show_err . fst) 
            <$> list_file_obligations' path
        if i < size xs then do
            let pos = snd $ snd $ i `elemAt` xs
            lookupSequent' (label lbl) pos
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
    let hide
            | hide_error_path = L.replace (p ++ ":") "error "
            | otherwise       = id
    return $ either 
        (hide . unlines . L.map report)
        (const $ "no errors")
        m

parse_machine :: FilePath -> Int -> IO (Either [Error] Machine)
parse_machine path n = runEitherT $ parse_machine' path n

parse_machine' :: FilePath -> Int -> EitherT [Error] IO Machine
parse_machine' fn i = lookup i =<< parse' fn

parse :: FilePath -> IO (Either [Error] [Machine])
parse path = do
    p <- getCurrentDirectory
    let mapError = traverse.traverseLineInfo.filename %~ drop (length p)
        f = ascElems . M.map fst
    (mapBoth mapError f . fst) <$> list_file_obligations' path

parse' :: FilePath -> EitherT [Error] IO [Machine]
parse' = EitherT . parse

verify_thy :: FilePath -> String -> IO POResult
verify_thy path name = makeReport' empty $ do
        r <- EitherT $ snd <$> list_file_obligations' path
        let pos = snd $ r ! name
        res <- lift $ try (verify_all pos)
        case res of
            Right res -> return (unlines $ L.map (\(k,r) -> success r ++ show k) $ toAscList res, pos)
            Left e -> return (show (e :: SomeException),pos)
    where
        success True  = "  o  "
        success False = " xxx "

get_system :: FilePath -> EitherT String IO System
get_system path = do
    EitherT $ either (Left . show_err) Right 
        <$> parse_system path

lookup :: (?loc :: CallStack,Monad m,Ixed f,Show (Index f)) => Index f -> f -> EitherT [Error] m (IxValue f)
lookup k m = maybe (left $ errorTrace [$__FILE__] ?loc (show k)) return $ m^?ix k
