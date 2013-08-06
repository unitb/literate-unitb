{-# LANGUAGE DeriveDataTypeable, BangPatterns #-} 

module Z3.Z3 
    ( module Z3.Def
    , module Z3.Const
    , ProofObligation ( .. )
    , Validity ( .. )
    , Satisfiability ( .. )
    , discharge, verify
    , Context ( .. )
    , mk_context
    , empty_ctx
    , merge_all_ctx, merge_ctx
    , merge_all, merge --, entails
    , entailment
    , var_decl, free_vars
    , z3_code
    , Tree ( .. )
    , Symbol ( .. )
    , Command ( .. )
    )
where

    -- Modules
import Z3.Def
import Z3.Const

    -- Libraries
import Control.Monad
import Control.Applicative hiding ( empty, Const )
    -- for the operator <|>

import Data.Char
import Data.List hiding (union)
import Data.Map as M hiding (map,filter,foldl)
import Data.Typeable
 
import System.Cmd
import System.Exit
import System.IO
import System.IO.Unsafe
import System.Process

import Utilities.Format

--match_type BOOL BOOL = True
--match_type INT INT = True
--match_type REAL REAL = True
--match_type (SET t0) (SET t1) = match_type t0 t1
--match_type (ARRAY t0 t1) (ARRAY t2 t3) = match_type t0 t2 && match_type t1 t3
--match_type (GENERIC x) (GENERIC y) = x == y
--match_type (USER_DEFINED x xs) (USER_DEFINED y ys) = 
--        x == y && length xs == length ys && all (uncurry match_type) (zip xs ys)
--match_type _ _ = False

--z3_path = "./bin/z3"
z3_path = "/Users/simonhudon/Downloads/z3-4.3.2.5b5a474b5443-x64-osx-10.8.2/bin/z3"

instance Tree Command where
    as_tree (Decl d)      = as_tree d
    as_tree (Assert xp)   = List [Str "assert", as_tree xp]
    as_tree (CheckSat _)  = List [Str "check-sat-using", 
                                    List (Str "or-else" : map strat
                                        [ Str "qe" 
                                        , Str "skip"
                                        , List 
                                            [ Str "using-params"
                                            , Str "simplify"
                                            , Str ":expand-power"
                                            , Str "true"] ] ) ]
        where
            strat t = List [Str "then", t, Str "smt"]
--    as_tree (CheckSat True)  = List [Str "check-sat-using", 
--                                    List [Str "then", Str "qe", Str "smt"] ]
--    as_tree (CheckSat False) = List [Str "check-sat"]
    as_tree GetModel      = List [Str "get-model"]
    rewrite' = id

feed_z3 :: String -> IO (ExitCode, String, String)
feed_z3 xs = do
        let c = (shell (z3_path ++ " -smt2 -in -T:1")) { 
            std_out = CreatePipe,
            std_in = CreatePipe,
            std_err = CreatePipe } 
        (Just stdin,Just stdout,Just stderr,ph) <- createProcess c
        hPutStr stdin xs
        b <- hIsOpen stdin 
        out <- hGetContents stdout
        err <- hGetContents stderr
        hClose stdin
--        let !() = unsafePerformIO (putStrLn "checkpoint 10")
        st <- waitForProcess ph
--        let !() = unsafePerformIO (putStrLn "checkpoint 11")
        return (st, out, err)
        
data Satisfiability = Sat | Unsat | SatUnknown
    deriving (Show, Typeable)

data Validity = Valid | Invalid | ValUnknown
    deriving (Show, Eq, Typeable)

data ProofObligation = ProofObligation Context [Expr] Bool Expr
    deriving Eq

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
            f (x, DefSort y z xs _) = f (x, Sort y z $ length xs)
            f (x, Sort y z 0) = z
            f (x, Sort y z n) = format "{0} [{1}]" z (intersperse ',' $ map chr $ take n [ord 'a' ..]) 
                --[" ++ intercalate "," zs ++ "]"

fold_expr f x (Word _)          = x
fold_expr f x (Const _ _ _)     = x
fold_expr f x (FunApp _ xs)     = foldl f x xs
fold_expr f x (Binder _ _ xp)   = f x xp

free_vars :: Context -> Expr -> Map String Var
free_vars (Context _ _ _ _ dum) e = fromList $ f [] e
    where
        f xs (Word v@(Var n t))
            | n `member` dum = (n,v):xs
            | otherwise      = xs
        f xs v = fold_expr f xs v

data Context = Context 
        (Map String Sort) -- sorts
        (Map String Var)  -- constants
        (Map String Fun)  -- functions and operators
        (Map String Def)  -- transparent definitions
        (Map String Var)  -- dummies
    deriving (Show,Eq)

empty_ctx = Context empty empty empty empty empty

var_decl :: String -> Context -> Maybe Var
var_decl s (Context _ m _ _ d) = 
    M.lookup s m <|> M.lookup s d

from_decl (FunDecl xs n ps r)  = Left (Fun xs n ps r)
from_decl (ConstDecl n t)      = Right (Var n t)
from_decl (FunDef xs n ps r _) = Left (Fun xs n (map (\(Var _ t) -> t) ps) r)

mk_context :: [Decl] -> Context
mk_context (x:xs) = 
        case mk_context xs of
            Context ss vs fs defs dums -> 
                case x of
                    ConstDecl n t -> 
                        Context 
                            ss (M.insert n (Var n t) vs) 
                            fs defs dums
                    FunDecl gs n ps t -> 
                        Context 
                            ss vs 
                            (M.insert n (Fun gs n ps t) fs)
                            defs dums
                    FunDef gs n ps t e -> 
                        Context 
                            ss vs fs 
                            (M.insert n (Def gs n ps t e) defs) 
                            dums
mk_context [] = Context empty empty empty empty empty

merge_ctx (Context ss0 vs0 fs0 ds0 dum0) (Context ss1 vs1 fs1 ds1 dum1) = 
        Context 
            (ss0 `merge` ss1) 
            (vs0 `merge` vs1) 
            (fs0 `merge` fs1) 
            (ds0 `merge` ds1)
            (dum0 `merge` dum1)
merge_all_ctx cs = Context 
        (merge_all $ map f0 cs) 
        (merge_all $ map f1 cs)
        (merge_all $ map f2 cs)
        (merge_all $ map f3 cs)
        (merge_all $ map f4 cs)
    where
        f0 (Context x _ _ _ _) = x
        f1 (Context _ x _ _ _) = x
        f2 (Context _ _ x _ _) = x
        f3 (Context _ _ _ x _) = x
        f4 (Context _ _ _ _ x) = x

class Symbol a where
    decl :: a -> [Decl]

instance Symbol Sort where
    decl s = [SortDecl s]

instance Symbol Fun where
    decl (Fun xs name params ret) = [FunDecl xs name params ret]

instance Symbol Var where
    decl (Var name typ)        = [ConstDecl name typ]

instance Symbol Def where
    decl (Def xs name ps typ ex)  = [FunDef xs name ps typ ex]

instance Symbol Context where
    decl (Context sorts cons fun defs dums) = 
                concatMap decl (elems sorts)
            ++  concatMap decl (elems (cons `merge` dums)) 
            ++  concatMap decl (elems fun) 
            ++  concatMap decl (elems defs) 
--            ++  concatMap decl (elems dums) 

merge m0 m1 = unionWithKey f m0 m1
    where
        f k x y
            | x == y = x
            | x /= y = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

merge_all ms = foldl (unionWithKey f) empty ms
    where
        f k x y
            | x == y = x
            | x /= y = error $ format "conflicting declaration for key {0}: {1} {2}" k x y

z3_code (ProofObligation d assume exist assert) = 
    (      (map Decl $ decl d)
        ++ map Assert assume 
        ++ [Assert (znot assert)]
        ++ [CheckSat exist] )

discharge :: ProofObligation -> IO Validity
discharge po = do
    s <- verify $ z3_code po
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
                  
--        po = ProofObligation 
--            (Context 
--                (srt0 `merge` srt1) 
--                (cons0 `merge` cons1) 
--                (fun0 `merge` fun1) 
--                (def0 `merge` def1)
--                (dum0 `merge` dum1))
--            (zimplies (zall xs0) xp0:xs1)
--            ex1
--            xp1 
--            (zforall (elems cons1) (zimplies (zall xs1) xp1))

