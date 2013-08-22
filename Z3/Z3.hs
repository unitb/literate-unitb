{-# LANGUAGE DeriveDataTypeable, BangPatterns #-} 

module Z3.Z3 
    ( module Z3.Def
    , module Z3.Const
    , ProofObligation ( .. )
    , Validity ( .. )
    , Satisfiability ( .. )
    , discharge, verify
    , Context ( .. )
    , entailment
    , var_decl 
    , free_vars
    , z3_code
    , Tree ( .. )
    , Symbol ( .. )
    , Command ( .. )
    )
where

    -- Modules
import Z3.Def
import Z3.Const
import Z3.Lambda

    -- Libraries
import Control.Applicative hiding ( empty, Const )
    -- for the operator <|>

import Data.Char
import Data.List hiding (union)
import Data.Map as M hiding (map,filter,foldl)
import Data.Typeable
 
import System.Exit
import System.IO
import System.Process

import Utilities.Format

--z3_path = "./bin/z3"
--z3_path = "/Users/simonhudon/Downloads/z3-4.3.2.5b5a474b5443-x64-osx-10.8.2/bin/z3"
z3_path = "z3"

instance Tree Command where
    as_tree (Decl d)      = as_tree d
    as_tree (Assert xp)   = List [Str "assert", as_tree xp]
    as_tree (CheckSat _)  = List [Str "check-sat-using", 
                                    List ( Str "or-else" 
                                         : map strat
                                         [ Str "qe" 
                                         , Str "simplify"
                                         , Str "skip"
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
        let c = (shell (z3_path ++ " -smt2 -in -T:2")) { 
            std_out = CreatePipe,
            std_in = CreatePipe,
            std_err = CreatePipe } 
        (Just stdin,Just stdout,Just stderr,ph) <- createProcess c
        hPutStr stdin xs
        b <- hIsOpen stdin 
        out <- hGetContents stdout
        err <- hGetContents stderr
        hClose stdin
        st <- waitForProcess ph
        return (st, out, err)
        
data Satisfiability = Sat | Unsat | SatUnknown
    deriving (Show, Typeable)

data Validity = Valid | Invalid | ValUnknown
    deriving (Show, Eq, Typeable)

instance Show ProofObligation where
    show (ProofObligation (Context ss vs fs ds dum) as _ g) =
            unlines (
                   map (" " ++)
                (  ["sort: " ++ intercalate ", " (map f $ toList ss)]
                ++ (map show $ elems fs)
                ++ (map show $ elems ds)
                ++ (map show $ elems vs)
                ++ map show as)
                ++ ["|----"," " ++ show g] )
        where
            f (x, IntSort) = ""
            f (x, BoolSort) = ""
            f (x, RealSort) = ""
            f (x, DefSort y z xs _) = f (x, Sort y z $ length xs)
            f (x, Sort y z 0) = z
            f (x, Sort y z n) = format "{0} [{1}]" z (intersperse ',' $ map chr $ take n [ord 'a' ..]) 

free_vars :: Context -> Expr -> Map String Var
free_vars (Context _ _ _ _ dum) e = fromList $ f [] e
    where
        f xs (Word v@(Var n t))
            | n `member` dum = (n,v):xs
            | otherwise      = xs
        f xs v = visit f xs v

var_decl :: String -> Context -> Maybe Var
var_decl s (Context _ m _ _ d) = 
    M.lookup s m <|> M.lookup s d

from_decl (FunDecl xs n ps r)  = Left (Fun xs n ps r)
from_decl (ConstDecl n t)      = Right (Var n t)
from_decl (FunDef xs n ps r _) = Left (Fun xs n (map (\(Var _ t) -> t) ps) r)

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
        ++ [CheckSat exist] )
    where
--        !() = unsafePerformIO (p
        (ProofObligation d assume exist assert) = delambdify po

discharge :: ProofObligation -> IO Validity
discharge po = do
    let code = z3_code po
--    let !() = unsafePerformIO (putStrLn $ format "code: {0}" code)
    s <- verify code
    return (case s of
        Right Sat -> Invalid
        Right Unsat -> Valid
        Right SatUnknown -> ValUnknown
        Left x -> Invalid)

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
    where
        err_msg code out err = 
            unlines (
                    (map (\(i,x) -> show i ++ " -\t" ++ x) $ zip [1..] $ lines code) 
                ++  ["output"]
                ++  (map ("> " ++) $ lines out)
                ++  ["err"]
                ++  (map ("> " ++) $  lines err) )


entailment  
    (ProofObligation (Context srt0 cons0 fun0 def0 dum0) xs0 ex0 xp0) 
    (ProofObligation (Context srt1 cons1 fun1 def1 dum1) xs1 ex1 xp1) = 
            (po0,po1)
    where
        po0 = ProofObligation 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            [xp0]
            ex1
            xp1 
        po1 = ProofObligation 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            xs1
            ex1
            (zall xs0)
