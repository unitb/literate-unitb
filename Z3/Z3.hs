module Z3.Z3 where

import Control.Monad

import Data.List hiding (union)
import Data.Map as M hiding (map,filter)
import Data.Typeable

import System.Cmd
import System.Exit
import System.IO
import System.IO.Unsafe
import System.Process

import Z3.Def
import Z3.Const

data StrList = List [StrList] | Str String

instance Show StrList where
    show (List xs) = "(" ++ intercalate " " (map show xs) ++ ")"
    show (Str s)   = s

class Tree a where
    as_tree :: a -> StrList
    
--instance Tree a => Show a where
--    show x = show $ as_tree x

match_type BOOL BOOL = True
match_type INT INT = True
match_type REAL REAL = True
match_type (ARRAY t0 t1) (ARRAY t2 t3) = match_type t0 t2 && match_type t1 t3

z3_path = "./bin/z3"

instance Show Quantifier where
    show Forall = "forall"
    show Exists = "exists"

instance Tree Expr where
    as_tree (Word (Var xs _)) = Str xs
    as_tree (Number n)        = Str $ show n
    as_tree (Const xs _)      = Str xs
    as_tree (FunApp (Fun name _ _) ts)  = 
        List (Str name : (map as_tree ts))
    as_tree (Binder q xs xp)  = List [
        Str $ show q, 
        List $ map as_tree xs,
        as_tree xp ]

instance Tree Type where
    as_tree BOOL = Str "Bool"
    as_tree INT  = Str "Int"
    as_tree REAL = Str "Real"
    as_tree (ARRAY t0 t1) = List [Str "Array", as_tree t0, as_tree t1]
    as_tree (GENERIC x) = Str x

instance Tree Decl where
    as_tree (FunDecl name dom ran) =
            List [ Str "declare-fun", 
                Str name, 
                (List $ map as_tree dom), 
                (as_tree ran) ]
    as_tree (ConstDecl n t) =
            List [ Str "declare-const", Str n, as_tree t ]
    as_tree (FunDef name dom ran val) =
            List [ Str "define-fun", 
                Str name, 
                (List $ map as_tree dom), 
                (as_tree ran),
                (as_tree val) ]

instance Tree Command where
    as_tree (Decl d)      = as_tree d
    as_tree (Assert xp)   = List [Str "assert", as_tree xp]
    as_tree (CheckSat _)  = List [Str "check-sat-using", 
                                    List [Str "or-else", 
                                        strat $ Str "qe", 
                                        strat $ Str "skip",
                                        strat $ List [
                                            Str "using-params",
                                            Str "simplify",
                                            Str ":expand-power",
                                            Str "true"] ] ]
        where
            strat t = List [Str "then", t, Str "smt"]
--    as_tree (CheckSat True)  = List [Str "check-sat-using", 
--                                    List [Str "then", Str "qe", Str "smt"] ]
--    as_tree (CheckSat False) = List [Str "check-sat"]
    as_tree GetModel      = List [Str "get-model"]
                
instance Tree Var where
    as_tree (Var vn vt) = List [Str vn, as_tree vt]

--instance Tree x => Show x where
--    show x = show $ as_tree x

instance Show Var where
    show (Var n t) = n ++ ": " ++ show (as_tree t)

instance Show Fun where
    show (Fun n ts t) = n ++ ": " 
        ++ intercalate " x " (map (show . as_tree) ts)
        ++ " -> " ++ show (as_tree t)

instance Show Def where
    show (Def n ps t e) = n ++ ": " 
        ++ intercalate " x " (map (show . as_tree) ps)
        ++ " -> " ++ show (as_tree t)
        ++ "  =  " ++ show (as_tree e)



instance Show Expr where
    show e = show $ as_tree e

--data StrList = List [StrList] | Str String
--
--parse :: Int -> [(Char, Int)] -> [(Char, Int)] -> Int -> Maybe [StrList]
--parse xs ys = 
--
--trim :: Int -> [(Char, Int)] -> Int -> (Int, [(Char,Int)])
--trim n [] m = (n, [])
--trim 
--
--tree xs = parse 1 ys (reverse ys) (length ys)
--    where
--        ys = zip xs [1..]

feed_z3 :: String -> IO (ExitCode, String, String)
feed_z3 xs = do
        let c = (shell (z3_path ++ " -smt2 -in ")) { 
            std_out = CreatePipe,
            std_in = CreatePipe,
            std_err = CreatePipe } 
        (Just stdin,Just stdout,Just stderr,ph) <- createProcess c
--        putStrLn xs
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

data ProofObligation = ProofObligation Context [Expr] Bool Expr

instance Show ProofObligation where
    show (ProofObligation (Context vs fs ds) as _ g) =
        unlines (
               map (" " ++)
            (  (map show $ elems fs)
            ++ (map show $ elems ds)
            ++ (map show $ elems vs)
            ++ map show as)
            ++ ["|----"," " ++ show g] )

data Context = Context (Map String Var) (Map String Fun) (Map String Def)

var_decl :: String -> Context -> Maybe Var
var_decl s (Context m _ _) = M.lookup s m

from_decl (FunDecl n ps r) = Left (Fun n ps r)
from_decl (ConstDecl n t) = Right (Var n t)
from_decl (FunDef n ps r _) = Left (Fun n (map (\(Var _ t) -> t) ps) r)

context :: [Decl] -> Context
context (x:xs) = 
        case context xs of
            Context vs fs defs -> 
                case x of
                    ConstDecl n t -> Context (M.insert n (Var n t) vs) fs defs
                    FunDecl n ps t -> Context vs (M.insert n (Fun n ps t) fs) defs
                    FunDef n ps t e -> Context vs fs (M.insert n (Def n ps t e) defs)
context [] = Context empty empty empty

merge_ctx (Context vs0 fs0 ds0) (Context vs1 fs1 ds1) = 
        Context (vs0 `merge` vs1) (fs0 `merge` fs1) (ds0 `merge` ds1)
merge_all_ctx cs = Context 
        (merge_all $ map f cs) 
        (merge_all $ map g cs)
        (merge_all $ map h cs)
    where
        f (Context x _ _) = x
        g (Context _ x _) = x
        h (Context _ _ x) = x

class Symbol a where
    decl :: a -> [Decl]

instance Symbol Fun where
    decl (Fun name params ret) = [FunDecl name params ret]

instance Symbol Var where
    decl (Var name typ)        = [ConstDecl name typ]

instance Symbol Def where
    decl (Def name ps typ ex)  = [FunDef name ps typ ex]

instance Symbol Context where
    decl (Context cons fun defs) = 
                concatMap decl (elems cons) 
            ++  concatMap decl (elems fun) 
            ++  concatMap decl (elems defs) 

class Named n where
    name    :: n -> String
    as_pair :: n -> (String, n)
    as_pair n = (name n, n)

instance Named Fun where
    name (Fun x _ _) = x

instance Named Var where
    name (Var x _) = x

merge m0 m1 = unionWith f m0 m1
    where
        f x y
            | x == y = x
            | x /= y = error "conflicting declaration"

merge_all ms = unionsWith f ms
    where
        f x y
            | x == y = x
            | x /= y = error "conflicting declaration"

z3_code (ProofObligation d assume exist assert) = 
    ( (map Decl $ decl d)
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
--        putStrLn $ show $ f (xs !! 3)
        let code = (unlines $ (map (show . as_tree) xs))
        (_,out,err) <- feed_z3 code
        let ln = lines out
        r <- if ln == [] || 
                (   head ln /= "sat"
                    && head ln /= "unsat"
                    && head ln /= "unknown") then do
--            putStrLn $ err_msg code out err
            return $ Left ("error: " ++ err ++ out)
        else if head ln == "sat" then do
--            putStrLn $ err_msg code out err
--            putStrLn $ unlines $ tail ln
            return $ Right Sat
        else if head ln == "unsat" then 
            return $ Right Unsat
        else if head ln == "unknown" then do
--            putStrLn $ err_msg code out err
            return $ Right SatUnknown
        else do
--                forM (zip [1..] $ lines code) print
--                putStrLn out
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
--        f (Assert (FunApp fn (FunApp x xs:_)))
--              = "assert: " ++ show x ++ " " ++ show (map as_tree xs)
--                -- ++ show (length xs) ++ " " ++ show fn --(map as_tree xs)
--        f (Assert (FunApp fn xs))    = "assert "
--        f (Assert (Binder _ xs _))   = "assert: quantifier" -- ++ show (length xs)
--        f (Assert (Word _))          = "assert: word"
--        f (Assert (Number _))        = "assert: number"
--        f (Assert (Const _ _))       = "assert: const"
--        f (CheckSat x) = "checksat"
--        f (Decl x)     = "decl"
--        f (GetModel)   = "get-model"

entails 
    (ProofObligation (Context cons0 fun0 def0) xs0 ex0 xp0) 
    (ProofObligation (Context cons1 fun1 def1) xs1 ex1 xp1) = 
            discharge $ po
    where
        po = ProofObligation 
            (Context empty (fun0 `merge` fun1) (def0 `merge` def1))
            [zforall (elems cons0) (zimplies (zall xs0) xp0)]
            ex1
            (zforall (elems cons1) (zimplies (zall xs1) xp1))

--    system "./z3"
--    let c = shell "./z3 source.z"
--    createProcess c
--    putStrLn "all"
--    withFile "file.txt" WriteMode (\h -> do
--        let c = (shell "./z3 -smt2 source.z") { std_out = UseHandle h } 
--        (_,_,_,ph) <- createProcess c
--        waitForProcess ph)