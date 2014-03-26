{-# LANGUAGE TupleSections #-}
module Code.Synthesis where

    -- Modules
import Logic.Const
import Logic.Expr
import Logic.Classes

import Theories.SetTheory

import UnitB.AST

    -- Libraries
import Control.Monad

import Data.Maybe
import Data.List as L hiding (inits)
import Data.Map as M
import Data.Set

import Utilities.Format

data Program = 
        Event Event 
        | Conditional (Set Expr) [(Expr, Program)]
        | Sequence  (Set Expr) [([Expr], Program)]
        | Loop (Set Expr) Expr Program Program

type_code :: Type -> Either String String
type_code t = 
            case t of
                USER_DEFINED s []
                    | s == IntSort ->  return "Int"
                    | s == BoolSort -> return "Bool"
                USER_DEFINED s [t]
                    | s == set_sort -> do
                        c <- type_code t
                        return $ format "S.Set ({0})" c
                USER_DEFINED s [t0,t1]
                    | s == fun_sort -> do
                        c0 <- type_code t0
                        c1 <- type_code t1
                        return $ format 
                            "M.Map ({0}) ({1})" c0 c1
                _ -> Left $ format "unrecognized type: {0}" t
                    
eval_expr :: Machine -> Expr -> Either String String
eval_expr m e =
        case e of
            Word (Var n _)
                | n `M.member` variables m -> return $ "v_" ++ n
                | otherwise              -> return $ "c_" ++ n
            Const _ n _    
                | n == "empty-fun" -> return "M.empty"
                | n == "empty-set" -> return "S.empty"
                | otherwise        -> return n
            FunApp f0 [e0,FunApp f1 [e1,e2]] 
                | name f0 == "ovl" && name f1 == "mk-fun" -> do
                    c0 <- eval_expr m e0
                    c1 <- eval_expr m e1
                    c2 <- eval_expr m e2
                    return $ format "(M.insert {1} {2} {0})" c0 c1 c2
            FunApp f [e0,e1] 
                | name f == "=" -> do
                    c0 <- eval_expr m e0
                    c1 <- eval_expr m e1
                    return $ format "({0} == {1})" c0 c1
                | name f == "+" -> do
                    c0 <- eval_expr m e0
                    c1 <- eval_expr m e1
                    return $ format "({0} + {1})" c0 c1
                | name f == "<" -> do
                    c0 <- eval_expr m e0
                    c1 <- eval_expr m e1
                    return $ format "({0} < {1})" c0 c1
                | name f == "ovl" -> do
                    c0 <- eval_expr m e0
                    c1 <- eval_expr m e1
                    return $ format "(M.union {0} {1})" c0 c1
                | name f == "mk-fun" -> do
                    c0 <- eval_expr m e0
                    c1 <- eval_expr m e1
                    return $ format "(M.singleton {0} {1})" c0 c1
            _ -> Left $ format "unrecognized expression: {0}" e

struct :: Machine -> Either String [Char]
struct m = do
        code <- attr
        return $ "data State = State\n    { " ++ code ++ " }"
    where
        attr = do 
            code <- mapM decl $ 
                           L.map ("v",) (M.elems $ variables m) 
--                        ++ L.map ("c",) (M.elems $ consts $ theory m)
            return $ intercalate "\n    , " code
        decl (pre,Var y t) = do
            code <- type_code t
            return $ format "{2}_{0} :: {1}" y code (pre :: String)

assign_code :: Machine -> Expr -> Either String [String]
assign_code m e =
        case e of
            FunApp f [Word (Var n _),e0]
                    |      pre `M.member` variables m 
                        && suff == "@prime"
                        && name f == "=" -> do
                                c0 <- eval_expr m e0
                                return [format "v_{0} = {1}" pre c0]
                where
                    (pre,suff) = splitAt (length n - length "@prime") n
            FunApp f es
                    | name f == "and" -> do
                        rs <- mapM (assign_code m) es
                        return $ concat rs
            _ -> Left $ format "assignment is not in a canonical form: {0}" e

init_value_code :: Machine -> Expr -> Either String [String]
init_value_code m e =
        case e of
            FunApp f [Word (Var n _),e0]
                    |      n `M.member` variables m 
                        && name f == "=" -> do
                                c0 <- eval_expr m e0
                                return [format "v_{0} = {1}" n c0]
            FunApp f es
                    | name f == "and" -> do
                        rs <- mapM (init_value_code m) es
                        return $ concat rs
            _ -> Left $ format "initialization is not in a canonical form: {0}" e

event_code :: Machine -> Event -> Either String String
event_code m e = do
        unless (M.null $ params e) $ Left "non null number of parameters"
        unless (M.null $ indices e) $ Left "non null number of indices"
        unless (isNothing $ fine $ new_sched e) $ Left "event has a fine schedule"
        grd  <- eval_expr m $ zall $ M.elems $ coarse $ new_sched e
        acts <- mapM (assign_code m) $ M.elems $ action e
        return $ format 
            (unlines $
                [ "modify $ \\s'@(State { .. }) ->" 
                , "  if {0} then"
                , "    s' { {1} }"
                , "  else s'"
                ]) grd (intercalate "\n       , " $ concat acts)

init_code :: Machine -> Either String String
init_code m = do
        acts <- mapM (init_value_code m) $ M.elems $ inits m
        return $ format 
            (unlines $ 
                [ "s' = State"
                , "       { {0} }" 
                ]) (intercalate "\n       , " $ concat acts)
                

indent :: Int -> String -> String
indent n xs = unlines $ L.map (take n (repeat ' ') ++) $ lines xs

machine_code :: String -> Machine -> Expr -> Either String String
machine_code name m exit = do
        let args = concatMap (" c_" ++) $ M.keys $ consts $ theory m
        exitc <- eval_expr m exit
        evts  <- mapM (event_code m) $ M.elems $ events m
        let prog = indent 25 $ concat evts
        inits <- init_code m
        let new_inits = indent 8 $ inits
        return $ format (unlines 
                    [ "{0}{1} = flip execState s' $ fix $ \\proc' -> do"
                    , "                      (State { .. }) <- get"
                    , "                      if {2} then return ()"
                    , "                      else do"
                    , "{3}" ++
                      "                         proc'"
                    , "    where"
                    , "{4}"
                    ] ) name args exitc prog new_inits

source_file :: String -> Machine -> Expr -> Either String String
source_file name m exit = do
        str <- struct m
        mch <- machine_code name m exit
        return $ format (unlines
                    [ "{-# LANGUAGE RecordWildCards #-}"
                    , "import Data.Map as M"
                    , "import Data.Set as S"
                    , "import Control.Monad.State"
                    , ""
                    , "{0}"
                    , ""
                    , "{1}"
                    ]) str mch 
