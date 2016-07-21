{-# LANGUAGE BangPatterns, RecordWildCards, OverloadedStrings #-} 
module Z3.Z3 
    ( Sequent
    , Validity ( .. )
    , Satisfiability ( .. )
    , discharge_all
    , discharge, verify
    , dischargeBoth
    , Context
    , entailment
    , var_decl 
    , free_vars
    , z3_code
    , z3_version
    , Tree ( .. )
    , Symbol ( .. )
    , Command ( .. )
    , smoke_test
    , discharge_on
    , pretty_print'
    , to_fol_ctx
    , patterns
    , match_all
    , map_failures
    , match_some, one_point
    , apply_monotonicity
    , remove_type_vars
    , check_z3_bin )
where

    -- Modules
import Logic.Expr hiding ((</>))
import Logic.Expr.Declaration
import Logic.Proof
import Logic.Proof.Monad

import Z3.Version

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Lens hiding (Context,Context',List)

import Control.Concurrent
import Control.Concurrent.SSem

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Precondition

import Data.Char
import qualified Data.DList as D
import           Data.Either.Combinators
import           Data.List as L hiding (union)
import           Data.Monoid
import qualified Data.Set as S
import           Data.Typeable 

import GHC.Generics (Generic)

import System.Exit
import System.IO.Unsafe
import System.Process

import Text.Printf

import qualified Data.Map.Class as M

total_caps :: SSem
total_caps = unsafePerformIO $ new $ z3c_capacity z3_config

instance Tree Command where
    as_tree' = return . as_tree
    as_tree (Push)        = List [Str "push"]
    as_tree (Pop)         = List [Str "pop"]
    as_tree (Decl d)      = as_tree d
    as_tree (SetOption name b) = List 
                        [ Str "set-option"
                        , Str $ ':' : name
                        , Str $ map toLower b]
    as_tree GetUnsatCore  = List [Str "get-unsat-core"]
    as_tree (Assert xp _n) = List [Str "assert", f $ g xp]
        where
            g (Binder FOForall vs r t _) = 
                    List 
                        [ Str "forall"
                        , List $ map as_tree vs
                        , List 
                            [ Str "!"
                            , as_tree $ r `zimplies` t
                            , Str ":pattern"
                            , List $ map as_tree $ z3_pattern (S.fromList vs) t
                            ]
                        ]
            g e = as_tree e
            f x = x
            -- f x = case n of 
            --         Nothing -> x
            --         Just n  -> List [Str "!",x,Str ":named",Str n]
    as_tree (Comment str) = Str $ intercalate "\n" $ map ("; " ++) $ lines str
    as_tree (CheckSat)    = List [Str "check-sat-using", 
                                    strat
                                         [ [ Str "qe"
                                           , Str "smt" ]
                                         , [Str "simplify", Str "smt"]
                                         , [Str "skip", Str "smt"]
--                                         , Str "der"
                                         , [using_param 
                                              (Str "simplify")
                                              ":expand-power"
                                              "true" 
                                           , Str "smt"] ] ]
        where
--            strat ts = List $ Str "or-else" : map f ts ++ [List (map Str ["then", "simplify", "bit-blast", "sat"])]
            using_param str param val = List [ Str "using-params"
                                             , str
                                             , Str param
                                             , Str val]
            strat ts = List $ Str "or-else" : map f ts
            f t = List $ Str "then" : t --, Str "smt"]
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
    rewriteM _ = pure

z3_pattern :: S.Set FOVar -> FOExpr -> [FOExpr]
z3_pattern vs e = runReader (head e) False
    where
        head e'@(FunApp f [_,y])
            | view name f == fromString'' "=>" = do
                xs <- head y
                if null xs 
                    then lhs vs e'
                    else return xs
        head e = lhs vs e

        lhs vs (FunApp f xs)
            | view name f `elem` map fromString'' ["and","or","not","=>"]
                && vs `S.isSubsetOf` S.unions (map used_var xs) 
                = do
                    ps <- concat <$> mapM (lhs S.empty) xs
                    return $ if vs `S.isSubsetOf` S.unions (map used_var ps) 
                        then ps 
                        else []
        lhs vs (FunApp f xs@[x,_])
            | view name f == fromString'' "="     = do
                b  <- ask
                x' <- lhs vs x 
                local (const True) $
                    if (b || null x') then do
                        ps <- concat <$> mapM (lhs S.empty) xs
                        return $ if vs `S.isSubsetOf` S.unions (map used_var ps) 
                            then ps 
                            else []
                    else
                        return x'
        lhs _ (Word (Var _ _)) = return []
        lhs vs e 
            | vs `S.isSubsetOf` used_var e = return [e]
            | otherwise                    = return []

feed_z3 :: String -> Int -> IO (ExitCode, String, String)
feed_z3 = unsafePerformIO $ do
    b <- check_z3_bin
    unless b $ fail "bad z3 setup"
    return $ \xs n -> do
        -- -- Mock
        -- evaluate $ force xs
        -- return (ExitSuccess,"unsat","")
        -- -- END Mock
        (st,out,err) <- readProcessWithExitCode z3_path ["-smt2","-in","-T:" ++ show n] xs
        return (st, out, err)
        
data Satisfiability = Sat | Unsat | SatUnknown
    deriving (Show, Typeable, Eq, Generic)

data Validity = Valid | Invalid | ValUnknown
    deriving (Show, Eq, Typeable, Generic)

data Command = Decl 
        (FODecl FOQuantifier) 
        | Assert FOExpr (Maybe String)
        | SetOption String String
        | CheckSat 
        | GetUnsatCore
        | GetModel 
        | Push | Pop 
        | Comment String
    deriving (Generic)

z3_code :: Sequent -> String
z3_code = unlines . L.map pretty_print' . z3_commands

z3_commands :: Sequent -> [Command]
z3_commands po = D.toList
    (      D.fromList [] 
        <> D.fromList [SetOption "auto-config" "false"]
        <> D.fromList [SetOption "smt.timeout" $ show tout]
        -- ++ [SetOption "smt.mbqi" "false"]
        <> D.fromList (map Decl (concatMap decl [maybe_sort,null_sort] ))
        <> D.fromList (map Decl (decl d))
        <> D.fromList (zipWith (\x y -> Assert x $ Just $ "s" ++ show y) 
                assume [0..])
        <> D.concat (map (D.fromList.f) (zip (M.toAscList hyps) [0..]))
        <> D.fromList [Assert (znot assert) $ Just "goal"]
        <> D.fromList [CheckSat]
        <> D.fromList [] )
    where
        (Sequent tout _ d _ assume hyps assert) = firstOrderSequent po
        f ((lbl,xp),n) = [ Comment $ pretty lbl
                         , Assert xp $ Just $ "h" ++ show n]

smoke_test :: Label -> Sequent -> IO Validity
smoke_test lbl po = discharge lbl (po & goal .~ zfalse)



discharge_on :: Label -> Sequent -> IO (MVar (Either String Validity))
discharge_on lbl po = do
    res <- newEmptyMVar
    forkIO $ do
        r <- try (discharge' (Just default_timeout) lbl po)
        let f e = show (e :: SomeException)
            r'  = mapLeft f r
        putMVar res r'
    return res


discharge_all :: [(Label,Sequent)] -> IO [Validity]
discharge_all xs = do
        setNumCapabilities 8
--        forM xs discharge
        rs <- forM xs $ uncurry discharge_on
        rs <- forM (zip [0..] rs) $ \(i,ref) -> do
            res <- takeMVar ref
            either 
                (throwIO . Z3Exception i) 
                return
                res
        return rs

data Z3Exception = Z3Exception Int String
    deriving (Show,Typeable)

instance Exception Z3Exception

map_failures :: (Int -> Label) -> IO a -> IO a
map_failures po_name cmd = catch cmd $ \(Z3Exception i msg) -> do
        fail $ printf "during verification of %s:\n%s" (pretty $ po_name i) msg 

--subexpr :: TypeSystem t => AbsExpr t -> [AbsExpr t]
--subexpr e = reverse $ f [] e
--    where
--        f xs e = visit f (e:xs) e

--funapps :: TypeSystem t => AbsExpr t -> [(AbsExpr t, AbsFun t)]
--funapps e = reverse $ f [] e
--    where
--        f xs e@(FunApp fun _) = visit f ((e,fun):xs) e
--        f xs e                 = visit f xs e

--statement :: Expr -> Statement
--statement e = Statement pat e
--    where
--        types = S.elems $ used_types e
--        pat  = L.map (substitute_type_vars gen) $ L.filter hg pat
--        hg x = not $ S.null $ variables x
--            -- has generics
--        gen = M.fromList $ L.map f $ S.elems $ S.unions $ L.map variables types
--        f x = (x, GENERIC x)
--        
--specialize_stmt :: S.Set Type -> Statement -> Map Label Expr
--specialize_stmt types (Statement pat e) = fromList $ zip ys $ map (flip substitute_type_vars e) xs
--    where
--        xs = match_all pat (S.elems types)
--        ys = map f xs
--        f xs = label $ concatMap z3_decoration $ M.elems xs
--

discharge :: Label -> Sequent -> IO Validity
discharge lbl po = discharge' Nothing lbl po

dischargeBoth :: Label -> SequentWithWD -> IO (SequentWithWD' Validity)
dischargeBoth lbl pos = SequentWithWD
        <$> discharge' Nothing lbl (_wd pos)
        <*> discharge' Nothing lbl (_goal pos)

discharge' :: Maybe Int      -- Timeout in seconds
           -> Label
           -> Sequent        -- 
           -> IO Validity
discharge' n lbl po
    | (po^.goal) == ztrue = return Valid
    | otherwise = withSemN total_caps (fromIntegral $ po^.resource) $ do
        let code  = z3_commands $ po & timeout %~ (`div` 4)
            code' = z3_commands po
            t = fromMaybe default_timeout n
        s  <- verify lbl code t
        s' <- if s == Right SatUnknown 
            then verify lbl code' t
            else return s
        case s' of
            Right Sat -> return Invalid
            Right Unsat -> return Valid
            Right SatUnknown -> do
                return ValUnknown
            Left xs -> do
                fail $ "discharge: " ++ xs

log_count :: MVar Int
log_count = unsafePerformIO $ newMVar 0

verify :: Label -> [Command] -> Int -> IO (Either String Satisfiability)
verify lbl xs n = do
        let ys = concat $ map reverse $ groupBy eq xs
            code = unlines $ map (pretty . as_tree) ys
            eq x y = is_assert x && is_assert y
            is_assert (Assert _ _) = True
            is_assert _            = False
        (_,out,_err) <- feed_z3 code n
        let lns = lines out
            res = take 1 $ dropWhile ("WARNING" `isPrefixOf`) lns
        if length lns == 0 ||
            (length lns > 1 && lns ! 1 /= "timeout") ||
                (      res /= ["sat"]
                    && res /= ["unsat"]
                    && res /= ["unknown"]
                    && res /= ["timeout"]) then do
            let header = Comment $ pretty lbl
            n <- modifyMVar log_count $ 
                return . ((1+) &&& id)
            writeFile (printf "log%d-1.z3" n) (unlines $ map pretty_print' $ header : ys)
            return $ Right SatUnknown
        else if res == ["sat"] then do
            return $ Right Sat
        else if res == ["unsat"] then do
            return $ Right Unsat
        else if res == ["unknown"] then do
            return $ Right SatUnknown
        else if (res == ["timeout"]) then do
            return $ Right SatUnknown
        else
            fail "verify: incomplete conditional"

instance NFData Command
instance NFData Satisfiability
instance NFData Validity
