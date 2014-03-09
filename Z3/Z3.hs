{-# LANGUAGE DeriveDataTypeable, BangPatterns, RecordWildCards #-} 

module Z3.Z3 
    ( Sequent ( .. )
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
    , pretty_print
    , pretty_print'
    )
where

    -- Modules
import Logic.Expr
import Logic.Classes
import Logic.Const
import Logic.Label
import Logic.Lambda
import Logic.Sequent

    -- Libraries
import Control.Applicative hiding ( empty, Const )
    -- for the operator <|>
import Control.Concurrent
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import           Data.Function
import           Data.List hiding (union)
import           Data.Map as M hiding (map,filter,foldl, (\\))
import qualified Data.Map as M
import           Data.Typeable 

import           System.Exit
import           System.Process

z3_path :: String
z3_path = "z3"

instance Tree Command where
    as_tree (Push)        = List [Str "push"]
    as_tree (Pop)         = List [Str "pop"]
    as_tree (Decl d)      = as_tree d
    as_tree (Assert xp)   = List [Str "assert", as_tree xp]
    as_tree (Comment str) = Str $ intercalate "\n" $ map ("; " ++) $ lines str
    as_tree (CheckSat)    = List [Str "check-sat-using", 
                                    strat
                                         [ Str "qe" 
                                         , Str "simplify"
                                         , Str "skip"
--                                         , Str "der"
                                         , List 
                                             [ Str "using-params"
                                             , Str "simplify"
                                             , Str ":expand-power"
                                             , Str "true"] ] ] 
        where
--            strat ts = List $ Str "or-else" : map f ts ++ [List (map Str ["then", "simplify", "bit-blast", "sat"])]
            strat ts = List $ Str "or-else" : map f ts
            f t = List [Str "then", t, Str "smt"]
--            strat ts = List [Str "then", List $ Str "repeat" : [List $ Str "or-else" : ts], Str "smt"]
--    as_tree (CheckSat)    = List [Str "check-sat-using", 
--                                    List ( Str "or-else" 
--                                         : map strat
--                                         [ Str "qe" 
--                                         , Str "simplify"
----                                         , Str "der"
--                                         , List 
--                                             [ Str "using-params"
--                                             , Str "simplify"
--                                             , Str ":expand-power"
--                                             , Str "true"] ] 
--                                           ++ [ Str "smt" ]) ]
--        where
--            strat t = List [Str "try-for", Str "200", List [Str "then", t, Str "sat"] ]
    as_tree GetModel      = List [Str "get-model"]
    rewriteM' = id

feed_z3 :: String -> IO (ExitCode, String, String)
feed_z3 xs = do
        (st,out,err) <- readProcessWithExitCode z3_path ["-smt2","-in","-T:2"] xs
        return (st, out, err)
        
data Satisfiability = Sat | Unsat | SatUnknown
    deriving (Show, Typeable)

data Validity = Valid | Invalid | ValUnknown
    deriving (Show, Eq, Typeable)

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

data Command = Decl Decl | Assert Expr | CheckSat 
    | GetModel 
    | Push | Pop 
    | Comment String

z3_code :: Sequent -> [Command]
z3_code po = 
    (      []
        ++ map Decl (concatMap decl
               [ Datatype ["a"] "Maybe" 
                    [ ("Just", [("fromJust", GENERIC "a")])
                    , ("Nothing", []) ]
               , Datatype [] "Null"
                    [ ("null", []) ] ] )
        ++ map Decl (decl d)
        ++ map Assert (assume) 
        ++ concatMap f (toList hyps)
        ++ [Assert (znot assert)]
        ++ [CheckSat]
        ++ [] )
    where
--        !() = unsafePerformIO (p
        (Sequent d assume hyps assert) = delambdify po
        f (lbl,xp) = [Comment $ show lbl, Assert xp]

smoke_test :: Sequent -> IO Validity
smoke_test (Sequent a b c _) =
    discharge $ Sequent a b c zfalse

data Prover = Prover
        { inCh  :: Chan (Maybe (Int,Sequent))
        , outCh :: Chan (Int,Validity)
        , n_workers :: Int
        }

new_prover :: Int -> IO Prover
new_prover n_workers = do
        inCh  <- newChan
        outCh <- newChan
        forM_ [1 .. n_workers] $ \p ->
            forkOn p $ worker inCh outCh
        return Prover { .. }
    where
        worker inCh outCh = void $ do
            runMaybeT $ forever $ do
                cmd <- lift $ readChan inCh
                case cmd of
                    Just (tid, po) -> lift $ do
                        r <- discharge po
                        writeChan outCh (tid,r)
                    Nothing -> do
                        MaybeT $ return Nothing

destroy_prover :: Prover -> IO ()
destroy_prover (Prover { .. }) = do
        forM_ [1 .. n_workers] $ \_ ->
            writeChan inCh Nothing

discharge_on :: Prover -> (Int,Sequent) -> IO ()
discharge_on (Prover { .. }) po = do
        writeChan inCh $ Just po

read_result :: Prover -> IO (Int,Validity)
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
        return $ map snd $ sortBy (compare `on` fst) rs

discharge :: Sequent -> IO Validity
discharge po = do
        let code = z3_code po
        s <- verify code
        case s of
            Right Sat -> return Invalid
            Right Unsat -> return Valid
            Right SatUnknown -> do
                return ValUnknown
            Left xs -> do
                fail $ "discharge: " ++ xs

verify :: [Command] -> IO (Either String Satisfiability)
verify xs = do
        let !code = (unlines $ map (show . as_tree) xs)
        (_,out,err) <- feed_z3 code
        let ln = lines out
        r <- if ln == [] || 
                (      ln /= ["sat"]
                    && ln /= ["unsat"]
                    && ln /= ["unknown"]
                    && ln /= ["timeout"]) then do
            return $ Left ("error: " ++ err ++ out)
        else if ln == ["sat"] then do
            return $ Right Sat
        else if ln == ["unsat"] then 
            return $ Right Unsat
        else if ln == ["unknown"] then do
            return $ Right SatUnknown
        else do
            unless (ln == ["timeout"]) 
                $ error "verify: incomplete conditional"
            return $ Right SatUnknown
        return r

