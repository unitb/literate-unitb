{-# LANGUAGE DeriveDataTypeable, BangPatterns, RecordWildCards #-} 

module Z3.Z3 
    ( module Z3.Def
    , module Z3.Const
    , Sequent ( .. )
    , Validity ( .. )
    , Satisfiability ( .. )
    , discharge_all
    , discharge, verify
    , Context ( .. )
    , entailment
    , var_decl 
    , free_vars
    , z3_code
    , Tree ( .. )
    , Symbol ( .. )
    , Command ( .. )
    , smoke_test
    , Prover
    , new_prover
    , destroy_prover
    , discharge_on
    , read_result
    )
where

    -- Modules
import UnitB.Label

import Z3.Def
import Z3.Const
import Z3.Lambda

    -- Libraries
import Control.Applicative hiding ( empty, Const )
    -- for the operator <|>
import Control.Concurrent
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import Data.Char
import Data.Function
import Data.List hiding (union)
import Data.Map as M hiding (map,filter,foldl, (\\))
import 		qualified
	   Data.Map as M
import Data.Typeable 
import System.Exit
import System.Process

import Utilities.Format

--z3_path = "./bin/z3"
--z3_path = "/Users/simonhudon/Downloads/z3-4.3.2.5b5a474b5443-x64-osx-10.8.2/bin/z3"
z3_path = "z3"

instance Tree Command where
    as_tree (Decl d)      = as_tree d
    as_tree (Assert xp)   = List [Str "assert", as_tree xp]
    as_tree (CheckSat)    = List [Str "check-sat-using", 
                                    List ( Str "or-else" 
                                         : map strat
                                         [ Str "qe" 
                                         , Str "simplify"
                                         , Str "skip"
--                                         , Str "der"
                                         , List 
                                             [ Str "using-params"
                                             , Str "simplify"
                                             , Str ":expand-power"
                                             , Str "true"] ] ) ]
        where
            strat t = List [Str "then", t, Str "smt"]
    as_tree GetModel      = List [Str "get-model"]
    rewriteM' = id

feed_z3 :: String -> IO (ExitCode, String, String)
feed_z3 xs = do
        (st,out,err) <- readProcessWithExitCode z3_path ["-smt2","-in","-T:2"] xs
--        let c = (shell (z3_path ++ " -smt2 -in -T:2.5")) { 
--            std_out = CreatePipe,
--            std_in = CreatePipe,
--            std_err = CreatePipe } 
--        (Just stdin,Just stdout,Just stderr,ph) <- createProcess c
--        hPutStr stdin xs
----        b <- hIsOpen stdin 
--        out <- hGetContents stdout
--        err <- hGetContents stderr
--        hClose stdin
--        st <- waitForProcess ph
        return (st, out, err)
        
data Satisfiability = Sat | Unsat | SatUnknown
    deriving (Show, Typeable)

data Validity = Valid | Invalid | ValUnknown
    deriving (Show, Eq, Typeable)

instance Show Sequent where
    show (Sequent (Context ss vs fs ds _) as g) =
            unlines (
                   map (" " ++)
                (  ["sort: " ++ intercalate ", " (map f $ toList ss)]
                ++ (map show $ elems fs)
                ++ (map show $ elems ds)
                ++ (map show $ elems vs)
                ++ map show as)
                ++ ["|----"," " ++ show g] )
        where
            f (_, IntSort) = ""
            f (_, BoolSort) = ""
            f (_, RealSort) = ""
            f (x, DefSort y z xs _) = f (x, Sort y z $ length xs)
            f (_, Sort _ z 0) = z
            f (_, Sort _ z n) = format "{0} [{1}]" z (intersperse ',' $ map chr $ take n [ord 'a' ..]) 

free_vars :: Context -> Expr -> Map String Var
free_vars (Context _ _ _ _ dum) e = fromList $ f [] e
    where
        f xs (Word v@(Var n _))
            | n `member` dum = (n,v):xs
            | otherwise      = xs
        f xs v@(Binder _ vs _ _) = toList (fromList (visit f xs v) M.\\ symbol_table vs)
        f xs v = visit f xs v

var_decl :: String -> Context -> Maybe Var
var_decl s (Context _ m _ _ d) = 
    M.lookup s m <|> M.lookup s d

--from_decl (FunDecl xs n ps r)  = Left (Fun xs n ps r)
--from_decl (ConstDecl n t)      = Right (Var n t)
--from_decl (FunDef xs n ps r _) = Left (Fun xs n (map (\(Var _ t) -> t) ps) r)

z3_code po = 
    (      map Decl
               [ Datatype ["a"] "Maybe" 
                    [ ("Just", [("fromJust", GENERIC "a")])
                    , ("Nothing", []) ]
               , Datatype ["a","b"] "Pair" 
                    [ ("pair", 
                        [ ("first",  GENERIC "a")
                        , ("second", GENERIC "b") ]) ]
               , Datatype [] "Null"
                    [ ("null", []) ] ] 
        ++ (map Decl $ decl d)
        ++ map Assert assume 
        ++ [Assert (znot assert)]
        ++ [CheckSat] )
    where
--        !() = unsafePerformIO (p
        (Sequent d assume assert) = delambdify po

smoke_test :: Sequent -> IO Validity
smoke_test (Sequent a b _) =
    discharge $ Sequent a b zfalse

data Prover = Prover
        { inCh  :: Chan (Maybe (Int,Sequent))
        , outCh :: Chan (Int,Validity)
        , n_workers :: Int
        }

new_prover n_workers = do
        inCh  <- newChan
        outCh <- newChan
        forM_ [1 .. n_workers] $ \p ->
            forkOn p $ worker inCh outCh
        return Prover { .. }
    where
        worker inCh outCh = void $ do
--            (Just stdin,Just stdout,_,pcs) <- createProcess (shell "z3 -smt2 -in")
--                { std_in = CreatePipe
----                , std_out = CreatePipe
--                , std_out = CreatePipe }
--            hSetBinaryMode stdin False
--            hSetBinaryMode stdout False
--            hSetBuffering stdin LineBuffering
--            hSetBuffering stdout LineBuffering
----            hSetBinaryMode stderr False
            runMaybeT $ forever $ do
                cmd <- lift $ readChan inCh
                case cmd of
                    Just (tid, po) -> lift $ do
                        r <- discharge po
--                        let code = unlines 
--                                    (   ["(echo \"begin\")"]
--                                     ++ map (show . as_tree) (z3_code po)
--                                     ++ ["(echo \"end\")"] )
--                        hPutStr stdin code
--                        xs <- hGetLine stdout
--                        unless (xs == "begin") $ error "the first line of output should be begin"
--                        xs <- while (/= "end") $ 
--                            hGetLine stdout
--                        let r
--                                | xs == ["sat","end"]   = Invalid
--                                | xs == ["unsat","end"] = Valid
--                                | otherwise             = ValUnknown
                        writeChan outCh (tid,r)
                    Nothing -> do
--                        lift $ terminateProcess pcs
                        MaybeT $ return Nothing

destroy_prover (Prover { .. }) = do
        forM_ [1 .. n_workers] $ \_ ->
            writeChan inCh Nothing

discharge_on (Prover { .. }) po = do
        writeChan inCh $ Just po

read_result (Prover { .. }) = 
        readChan outCh

discharge_all :: [Sequent] -> IO [Validity]
discharge_all xs = do
        let ys = zip [0..] xs
        pr <- new_prover 8
        forkIO $ forM_ ys $ \task -> 
            discharge_on pr task
        rs <- forM ys $ \_ ->
            read_result pr
        destroy_prover pr
--        inCh  <- newChan
--        outCh <- newChan
--        xs <- forM [1 .. 8] $ \p -> 
--            forkOn p $ worker inCh outCh
--        forM_ ys $ \task -> 
--            writeChan inCh task
--        rs <- forM ys $ \_ ->
--            readChan outCh
--        forM_ xs $ killThread
        return $ map snd $ sortBy (compare `on` fst) rs
--    where
--        worker inCh outCh = forever $ do
--            (tid, po) <- readChan inCh
--            r <- discharge po
--            writeChan outCh (tid,r)        

discharge :: Sequent -> IO Validity
discharge po = do
    let code = z3_code po
--    let !() = unsafePerformIO (putStrLn $ format "code: {0}" code)
    s <- verify code
    return (case s of
        Right Sat -> Invalid
        Right Unsat -> Valid
        Right SatUnknown -> ValUnknown
        Left _ -> Invalid)

verify :: [Command] -> IO (Either String Satisfiability)
verify xs = do
        let !code = (unlines $ map (show . as_tree) xs)
        (_,out,err) <- feed_z3 code
        let ln = lines out
        r <- if ln == [] || 
                (   head ln /= "sat"
                    && head ln /= "unsat"
                    && head ln /= "unknown") then do
            return $ Left ("error: " ++ err ++ out)
        else if head ln == "sat" then do
            return $ Right Sat
        else if head ln == "unsat" then 
            return $ Right Unsat
        else if head ln == "unknown" then do
            return $ Right SatUnknown
        else do
            return $ Left out
        return r
--    where
--        err_msg code out err = 
--            unlines (
--                    (map (\(i,x) -> show i ++ " -\t" ++ x) $ zip [1..] $ lines code) 
--                ++  ["output"]
--                ++  (map ("> " ++) $ lines out)
--                ++  ["err"]
--                ++  (map ("> " ++) $  lines err) )


entailment  
    (Sequent (Context srt0 cons0 fun0 def0 dum0) xs0 xp0) 
    (Sequent (Context srt1 cons1 fun1 def1 dum1) xs1 xp1) = 
            (po0,po1)
    where
        po0 = Sequent 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            [xp0]
            xp1 
        po1 = Sequent 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            xs1
            (zall xs0)
