{-# LANGUAGE DeriveDataTypeable, BangPatterns, RecordWildCards #-} 

module Z3.Z3 
    ( Sequent
    , Validity ( .. )
    , Satisfiability ( .. )
    , discharge_all
    , discharge, verify
    , Context
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
    , pretty_print'
    , to_fol_ctx
    , patterns
    , match_all
    , map_failures
    , match_some, one_point
    , apply_monotonicity
    , remove_type_vars )
where

    -- Modules
import Logic.Expr
import Logic.Lambda
import Logic.Expr.Genericity ( Generic, variables )
import Logic.Proof

    -- Libraries
import Control.DeepSeq

import Control.Concurrent
import Control.Concurrent.SSem
import Control.Exception
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe

import           Data.Char
import           Data.List as L hiding (union)
import           Data.List.Ordered as OL hiding (member)
import           Data.Map as M (Map)
import qualified Data.Map as M
import qualified Data.Maybe as MM
import qualified Data.Set as S
import           Data.Typeable 

import           System.Exit
import           System.IO.Unsafe
import           System.Process

import           Utilities.Format

z3_path :: String
z3_path = "z3"

default_timeout :: Int
default_timeout = 5

instance Tree Command where
    as_tree (Push)        = List [Str "push"]
    as_tree (Pop)         = List [Str "pop"]
    as_tree (Decl d)      = as_tree d
    as_tree (SetOption name b) = List 
                        [ Str "set-option"
                        , Str $ ':' : name
                        , Str $ map toLower $ show b]
    as_tree GetUnsatCore  = List [Str "get-unsat-core"]
    as_tree (Assert xp _n) = List [Str "assert", f $ g xp]
        where
            g (Binder Forall vs r t) = 
                    List 
                        [ Str "forall"
                        , List $ map as_tree vs
                        , List 
                            [ Str "!"
                            , as_tree $ r `zimplies` t
                            , Str ":pattern"
                            , List $ map as_tree $ lhs vs (head t)
                            ]
                        ]
            g e = as_tree e
            lhs vs (FunApp f xs)
                | name f `elem` ["and","or","not"]
                       = concatMap (lhs vs) xs
            lhs vs (FunApp f [x,_])
                | name f == "="     = lhs vs x
            lhs _ (Word (Var _ _)) = []
            lhs vs e 
                | S.fromList vs `S.isSubsetOf` used_var e = [e]
                | otherwise                               = []
            head (FunApp f [_,y])
                | name f == "=>"    = head y
            head e = e
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
    rewriteM' = id

feed_z3 :: String -> Int -> IO (ExitCode, String, String)
feed_z3 xs n = do
        (st,out,err) <- readProcessWithExitCode z3_path ["-smt2","-in","-T:" ++ show n] xs
        return (st, out, err)
        
data Satisfiability = Sat | Unsat | SatUnknown
    deriving (Show, Typeable)

data Validity = Valid | Invalid | ValUnknown
    deriving (Show, Eq, Typeable)

data Command = Decl FODecl 
    | Assert FOExpr (Maybe String)
    | SetOption String Bool
    | CheckSat 
    | GetUnsatCore
    | GetModel 
    | Push | Pop 
    | Comment String

instance NFData Command where
    rnf (SetOption xs b) = rnf (xs,b)
    rnf (Decl d)     = rnf d 
    rnf (Assert e s) = rnf (e,s)
    rnf (CheckSat)   = ()
    rnf GetUnsatCore = ()
    rnf GetModel     = ()
    rnf Push         = ()
    rnf Pop          = ()
    rnf (Comment xs) = rnf xs

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
        ++ map (\(x,y) -> Assert x $ Just $ "s" ++ show y) 
               (zip assume [0..])
        ++ concatMap f (zip (M.toList hyps) [0..])
        ++ [Assert (znot assert) $ Just "goal"]
        ++ [CheckSat]
        ++ [] )
    where
--        !() = unsafePerformIO (p
        (Sequent d assume hyps assert) = remove_type_vars 
                    $ one_point
                    $ delambdify
                    $ apply_monotonicity po
        f ((lbl,xp),n) = [ Comment $ show lbl
                     , Assert xp $ Just $ "h" ++ show n]

one_point :: Sequent -> Sequent
one_point (Sequent a b c g) = Sequent a asm c g'
    where
        asm
            | g == g'   = b
            | otherwise = b ++ [znot g]
        g' = one_point_rule g

smoke_test :: Sequent -> IO Validity
smoke_test (Sequent a b c _) =
    discharge (Sequent a b c zfalse)

data Prover = Prover
        { inCh  :: Chan (Maybe (Int,Sequent))
--        , secCh :: Chan (Maybe (Int,Sequent))
        , outCh :: Chan (Int,Either String Validity)
        , n_workers :: Int
        }

new_prover :: Int -> IO Prover
new_prover n_workers = do
        setNumCapabilities 8
        inCh  <- newChan
--        secCh <- newChan
        outCh <- newChan
        let worker = void $ do
                runMaybeT $ forever $ do
                    cmd <- lift $ readChan inCh
                    case cmd of
                        Just (tid, po) -> lift $ do
                            r <- try (discharge' (Just default_timeout) po)
                            let f e = Left $ show (e :: SomeException)
                                r'  = either f Right r
                            writeChan outCh (tid,r')
                        Nothing -> do
                            MaybeT $ return Nothing
--            worker' = void $ do
--                runMaybeT $ forever $ do
--                    cmd <- lift $ readChan inCh
--                    case cmd of
--                        Just (tid, po) -> lift $ do
--                            r <- try (discharge po)
--                            let f e = Left $ show (e :: SomeException)
--                                r'  = either f Right r
--                            if r' == Right Valid then 
--                                writeChan outCh (tid,r')
--                            else
--                                writeChan secCh $ Just (tid,po)
--                        Nothing -> do
--                            MaybeT $ return Nothing
        forM_ [1 .. n_workers] $ \p ->
            forkOn p $ worker
--        forkIO worker
        return Prover { .. }

destroy_prover :: Prover -> IO ()
destroy_prover (Prover { .. }) = do
        forM_ [1 .. n_workers] $ \_ ->
            writeChan inCh Nothing
--        writeChan secCh Nothing


discharge_on :: Sequent -> IO (MVar (Either String Validity))
discharge_on po = do
    res <- newEmptyMVar
    forkIO $ withSem total_caps $ do
        r <- try (discharge' (Just default_timeout) po)
        let f e = Left $ show (e :: SomeException)
            r'  = either f Right r
        putMVar res r'
    return res

read_result :: Prover -> IO (Int,Either String Validity)
read_result (Prover { .. }) = 
        readChan outCh

total_caps :: SSem
total_caps = unsafePerformIO $ new 64

discharge_all :: [Sequent] -> IO [Validity]
discharge_all xs = do
        setNumCapabilities 8
--        forM xs discharge
        rs <- forM xs discharge_on
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
        fail $ format "during verification of {0}:\n{1}" (po_name i) msg 

--subexpr :: TypeSystem t => AbsExpr t -> [AbsExpr t]
--subexpr e = reverse $ f [] e
--    where
--        f xs e = visit f (e:xs) e

--funapps :: TypeSystem t => AbsExpr t -> [(AbsExpr t, AbsFun t)]
--funapps e = reverse $ f [] e
--    where
--        f xs e@(FunApp fun _) = visit f ((e,fun):xs) e
--        f xs e                 = visit f xs e

--mk_error :: (Expr -> Maybe FOExpr) -> Expr -> Maybe FOExpr
mk_error :: (Show a, Show c) => c -> (a -> Maybe b) -> a -> b
mk_error z f x = 
        case f x of
            Just y -> y
            Nothing -> error $ format "failed to strip type variables: {0}\n{1}" x z
    where
--        xs = funapps x
--        g (x,y) = format "{0} :: {1} ; {2}\n" x (type_of x) y :: String
--        ys = concatMap g xs

remove_type_vars :: Sequent -> FOSequent
remove_type_vars (Sequent ctx asm hyp g) = MM.fromJust $ do
    let vars  = variables g
        (Context sorts' _ _ _ _) = ctx
        sorts = M.keys sorts'
        as_type n = Gen $ USER_DEFINED (Sort n n 0) []
            -- new sorts are replacements for all the type variables
            -- present in the goal
        new_sorts = map as_type $ map (("G" ++) . show) [0..] `minus` sorts
        varm = M.fromList $ zip (S.elems vars) new_sorts
    g   <- return $ mk_error () strip_generics (substitute_type_vars varm g)
    let types = MM.catMaybes $ map type_strip_generics 
                    $ S.elems $ S.unions 
                    $ map used_types $ asm ++ M.elems hyp
        types' = S.fromList $ types `OL.union` S.elems (used_types g)
    _asm <- return $ map snd $ concatMap (gen_to_fol types' (label "")) asm
    h   <- return $ M.fromList $ concat $ M.elems $ M.mapWithKey (gen_to_fol types') hyp
    let types = S.unions $ map used_types $ g : _asm ++ M.elems h
    _ctx <- return $ to_fol_ctx types $ ctx
    return (Sequent _ctx _asm h g)


consistent :: (Eq b, Ord k) 
           => Map k b -> Map k b -> Bool
consistent x y = x `M.intersection` y == y `M.intersection` x

is_maybe :: Type -> Bool
is_maybe t = MM.isJust (unify t (maybe_type gA))
    where
        gA = GENERIC "a"

match_all :: [Type] -> [FOType] -> [Map String FOType]
match_all pat types = 
        foldM (\x p -> do
                t  <- types'
                m  <- MM.maybeToList $ unify p t
                ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
                let m' = M.fromList $ zip (M.keys m) ms
                    m''  = M.mapKeys (reverse . drop 2 . reverse) m'
                guard $ consistent m'' x
                return (m'' `M.union` x)
            ) M.empty pat'
    where
        pat' = filter (not . is_maybe) $ L.map f pat
        f (VARIABLE s) = GENERIC s
        f t = rewrite f t
        types' = map as_generic types

match_some :: [Type] -> [FOType] -> [Map String FOType]
match_some pat types = nubSort $ do -- map (M.map head) ms -- do
        ms <- foldM (\x (_,xs) -> do
                m <- xs
                guard $ consistent m x
                return (m `M.union` x)
            ) M.empty (M.toList ms')
--        ms <- forM (toList ms') $ \(k,xs) -> do
--            x <- xs
--            return (k,x)
--        let ms' = fromList ms
        guard $ M.keysSet ms == vars
        return ms
    where
        pat' = L.map f pat
        f (VARIABLE s) = GENERIC s
        f t = rewrite f t
        types' = map as_generic types
        vars = S.unions $ map generics pat'
        ms' = M.unionsWith (++) ms
--        ms :: [Map String [FOType]]
        ms :: [Map String [Map String FOType]]
        ms = do
            p  <- pat'
            t  <- types'
            m  <- MM.maybeToList $ unify p t
            ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
            let ms' = M.fromList $ zip (map (reverse . drop 2 . reverse) $ M.keys m) ms
            return $ M.map (const [ms']) ms' 

    -- instantiation patterns
patterns :: Generic a => a -> [Type]
patterns ts = pat
    where
        types = L.map g $ S.elems $ types_of ts
        pat  = L.map (substitute_type_vars gen) $ L.filter hg types
        hg x = not $ S.null $ variables x
            -- has generics
        gen = M.fromList $ L.map f $ S.elems $ S.unions $ L.map variables types
        f x = (x, GENERIC x)
        g (GENERIC s) = VARIABLE s
        g t = rewrite g t

    -- generic to first order
gen_to_fol :: S.Set FOType -> Label -> Expr -> [(Label,FOExpr)]
gen_to_fol types lbl e = -- with_tracing $ trace (show xs) $ 
        zip ys $ map inst xs
    where
        inst m = mk_error (S.unions $ map generics pat)
                    strip_generics $ substitute_type_vars (M.map as_generic m) e
        xs     = match_all pat (S.elems types)
        ys     = map f xs
        f xs   = composite_label [lbl, label $ concatMap z3_decoration $ M.elems xs]
        pat    = patterns e

to_fol_ctx :: S.Set FOType -> Context -> FOContext
to_fol_ctx types (Context s vars funs defs dums) = 
        Context s vars' funs' defs' dums'
    where
        vars' = M.map fv  vars
        funs' = decorated_table $ concatMap ff $ M.elems funs
        defs' = decorated_table $ concatMap fdf $ M.elems defs
        dums' = M.map fdm dums
        fv    = mk_error () var_strip_generics
        ff fun = map inst xs
            where
                pat    = patterns fun
                xs     = L.map (M.map as_generic) 
                            $ match_all pat (S.elems types)
                inst m = mk_error m fun_strip_generics $ substitute_type_vars m fun'
                fun' = substitute_types f fun
                f (GENERIC s) = VARIABLE s
                f t = rewrite f t
        fdf def = map inst xs -- M.fromJust . def_strip_generics
            where 
                pat    = patterns def
                xs     = L.map (M.map as_generic) 
                            $ match_all pat (S.elems types)
                inst m = mk_error m def_strip_generics $ substitute_type_vars m def'
                def' = substitute_types f def
                f (GENERIC s) = VARIABLE s
                f t = rewrite f t
        fdm = MM.fromJust . var_strip_generics

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
fresh :: String -> S.Set String -> String
fresh name xs = head $ ys `minus` S.elems xs
    where
        ys = name : map f [0..]
        f x = name ++ show x

discharge :: Sequent -> IO Validity
discharge po = discharge' Nothing po

differs_by_one :: Eq a => [a] -> [a] -> Maybe (Int,a,a)
differs_by_one xs ys = f $ zip [0..] $ zip xs ys
    where
        f [] = Nothing
        f ((i,(x,y)):xs) 
            | x == y        = f xs
            | all (uncurry (==) . snd) xs = Just (i,x,y)
            | otherwise     = Nothing

apply_monotonicity :: Sequent -> Sequent
apply_monotonicity po@(Sequent ctx asm h g) = maybe po id $
        let 
            h' = h
--            h' = M.insert (label $ fresh "~goal" $ S.map show $ keysSet h) (znot g) h 
            asm' = asm ++ [znot g]
            --asm' = znot g : asm
        in
        case g of
            Binder Forall (Var nam t:vs) rs ts -> do
                let (Context ss vars funs defs dums) = ctx
                    v   = Var (fresh nam $ 
                                      M.keysSet vars 
                            `S.union` M.keysSet funs
                            `S.union` M.keysSet defs) t
                    g'
                        | L.null vs = rs `zimplies` ts
                        | otherwise = zforall vs rs ts
                    ctx' = Context ss (M.insert (name v) v vars) funs defs dums
                return $ apply_monotonicity $ Sequent ctx' asm' h' 
                    (rename nam (name v) g')
            FunApp f [lhs, rhs] ->
                case (lhs,rhs) of
                    (Binder Forall vs r0 t0, Binder Forall us r1 t1) 
                        | vs == us && name f `elem` ["=","=>"] -> 
                            return $ apply_monotonicity (Sequent ctx asm' h' 
                                (zforall vs ztrue $ 
                                    FunApp f [zimplies r0 t0, zimplies r1 t1]))
                    (Binder Exists vs r0 t0, Binder Exists us r1 t1) 
                        | vs == us && name f `elem` ["=","=>"] -> 
                            return $ apply_monotonicity (Sequent ctx asm' h' 
                                (zforall vs ztrue $ 
                                    FunApp f [zand r0 t0, zand r1 t1]))
                    (FunApp g0 xs, FunApp g1 ys)
                        | length xs /= length ys || g0 /= g1 -> Nothing
                        | name f == "=" -> do
                            (_,x,y) <- differs_by_one xs ys
                            return $ apply_monotonicity (Sequent ctx asm' h' $ 
                                FunApp f [x, y])
                        | name g0 `elem` ["and","or","not","=>"] &&
                          name f == "=>" -> do
                                -- and(0,1), or(0,1), 
                                --      =>(1)       -> f.x => f.y -> x => y
                                -- not (0), =>(0)   -> f.x => f.y -> y => x
                                -- | arithmetic relations are not implement
                                -- <=(0)            -> f.x => f.y -> y <= x
                                -- <=(1)            -> f.x => f.y -> x <= y
                                -- +(0,1),-(0)      -> f.x <= f.y -> x <= y
                                -- -(1)             -> f.x <= f.y -> y <= x
                                -- | How would we treat the case of:
                                -- | context => a+b+x R a+b+y
                                -- | we need a means to distinguish an 
                                -- | implication that introduces contextual
                                -- | information
                            x <- mono (name f) (name g0) xs ys
                            return $ apply_monotonicity (Sequent ctx asm' h' x)
--                            let op = name g0
--                                mono i xs
--                                    | (op `elem` ["and","or"]) ||
--                                        (op == "=>" && i == 1)     = FunApp f xs
--                                    |  op == "not" ||
--                                        (op == "=>" && i == 0)     = FunApp f $ reverse xs
--                                    | otherwise                  = error $ "Z3.discharge': unexpected operator / position pair: " ++ op ++ ", " ++ show i
--                            in case differs_by_one xs ys of
--                                Just (i,x,y) -> 
--                                    apply_monotonicity (Sequent ctx asm h' $ 
--                                        mono i [x, y])
--                                Nothing -> 
--                                    po
                    _ -> Nothing
            _ -> Nothing
    where
        mono :: String -> String -> [Expr] -> [Expr] -> Maybe Expr
        mono rel fun xs ys = do
            f       <- M.lookup (rel, fun) m
            (i,x,y) <- differs_by_one xs ys
            g       <- f i
            return $ g x y
        m = M.fromList $
            [ (("=>","and"),const $ Just zimplies)
            , (("=>","or"),const $ Just zimplies)
            , (("=>","not"),const $ Just $ flip zimplies)
            , (("=>","=>"), \i -> Just $ if i == 0 
                                         then flip zimplies 
                                         else zimplies)
            , (("=>","<="), \i -> Just $ if i == 0 
                                         then flip zle 
                                         else zle)
            , (("<=","+"),const $ Just zle)
            , (("<=","-"), \i -> Just $ if i == 0 
                                         then flip zle 
                                         else zle)
            ]

discharge' :: Maybe Int      -- Timeout in seconds
           -> Sequent        -- 
           -> IO Validity
discharge' n po = do
        let code = z3_code po
        s <- verify code (maybe default_timeout id n)
        case s of
            Right Sat -> return Invalid
            Right Unsat -> return Valid
            Right SatUnknown -> do
                return ValUnknown
            Left xs -> do
                fail $ "discharge: " ++ xs

verify :: [Command] -> Int -> IO (Either String Satisfiability)
verify xs n = do
        let ys = concat $ map reverse $ groupBy eq xs
            !code = (unlines $ map (show . as_tree) ys) -- $ [Push] ++ xs ++ [Pop])
            eq x y = is_assert x && is_assert y
            is_assert (Assert _ _) = True
            is_assert _            = False
        (_,out,err) <- feed_z3 code n
        let lns = lines out
            res = take 1 lns
        if length lns == 0 ||
            (length lns > 1 && lns !! 1 /= "timeout") ||
                (      res /= ["sat"]
                    && res /= ["unsat"]
                    && res /= ["unknown"]
                    && res /= ["timeout"]) then do
            return $ Left ("error: \n" ++ err ++ out)
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

