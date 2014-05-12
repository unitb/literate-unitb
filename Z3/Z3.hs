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
    , pretty_print
    , pretty_print'
    , to_fol_ctx
    , patterns
    , match_all
    , match_some
    )
where

    -- Modules
import Logic.Expr
import Logic.Classes
import Logic.Const
import Logic.Genericity
import Logic.Label
import Logic.Lambda
import Logic.Sequent
import Logic.Type

    -- Libraries
import Control.Applicative hiding ( empty, Const )
    -- for the operator <|>
import Control.Concurrent
import Control.Exception
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import           Data.Function
import           Data.List as L hiding (union)
import           Data.List.Ordered as OL hiding (member)
import           Data.Map as M hiding (map,filter,foldl, (\\))
import qualified Data.Map as M
import qualified Data.Maybe as M ( fromJust, catMaybes
                                 , maybeToList, isJust )
import qualified Data.Set as S
import           Data.Typeable 

import           System.Exit
import           System.Process

import           Utilities.Format
import           Utilities.Trace

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

feed_z3 :: String -> Int -> IO (ExitCode, String, String)
feed_z3 xs n = do
        (st,out,err) <- readProcessWithExitCode z3_path ["-smt2","-in","-T:" ++ show n] xs
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

data Command = Decl FODecl | Assert FOExpr | CheckSat 
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
        (Sequent d assume hyps assert) = remove_type_vars 
                    $ delambdify
                    $ apply_monotonicity po
        f (lbl,xp) = [Comment $ show lbl, Assert xp]

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
        inCh  <- newChan
--        secCh <- newChan
        outCh <- newChan
        let worker = void $ do
                runMaybeT $ forever $ do
                    cmd <- lift $ readChan inCh
                    case cmd of
                        Just (tid, po) -> lift $ do
                            r <- try (discharge' (Just 4) po)
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

discharge_on :: Prover -> (Int,Sequent) -> IO ()
discharge_on (Prover { .. }) po = do
        writeChan inCh $ Just po

read_result :: Prover -> IO (Int,Either String Validity)
read_result (Prover { .. }) = 
        readChan outCh

discharge_all :: [Sequent] -> IO [Validity]
discharge_all xs = do
--        forM xs discharge
        let ys = zip [0..] xs
        pr <- new_prover 8
        forkIO $ forM_ ys $ \task -> 
            discharge_on pr task
        rs <- forM ys $ \_ ->
            read_result pr
        destroy_prover pr
        rs <- forM rs $ \(i,r) -> 
            either 
                error 
                (\x -> return (i,x)) 
                r
        return $ map snd $ sortBy (compare `on` fst) rs

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
remove_type_vars (Sequent ctx asm hyp g) = M.fromJust $ do
    let vars  = variables g
        (Context sorts' _ _ _ _) = ctx
        sorts = M.keys sorts'
        as_type n = Gen $ USER_DEFINED (Sort n n 0) []
            -- new sorts are replacements for all the type variables
            -- present in the goal
        new_sorts = map as_type $ map (("G" ++) . show) [0..] `minus` sorts
        varm = M.fromList $ zip (S.elems vars) new_sorts
    g   <- return $ mk_error () strip_generics (substitute_type_vars varm g)
    let types = M.catMaybes $ map type_strip_generics 
                    $ S.elems $ S.unions 
                    $ map used_types $ asm ++ elems hyp
        types' = S.fromList $ types `OL.union` S.elems (used_types g)
    asm <- return $ map snd $ concatMap (gen_to_fol types' (label "")) asm
    h   <- return $ fromList $ concat $ elems $ mapWithKey (gen_to_fol types') hyp
    let types = S.unions $ map used_types $ g : asm ++ elems h
    ctx <- return $ to_fol_ctx types ctx
    return (Sequent ctx asm h g)


consistent :: (Eq b, Ord k) 
           => Map k b -> Map k b -> Bool
consistent x y = x `intersection` y == y `intersection` x

is_maybe :: Type -> Bool
is_maybe t = M.isJust (unify t (maybe_type gA))
    where
        gA = GENERIC "a"

match_all :: [Type] -> [FOType] -> [Map String FOType]
match_all pat types = 
        foldM (\x p -> do
                t  <- types'
                m  <- M.maybeToList $ unify p t
                ms <- M.maybeToList $ mapM type_strip_generics (elems m) 
                let m' = M.fromList $ zip (keys m) ms
                let m  = M.mapKeys (reverse . drop 2 . reverse) m'
                guard $ consistent m x
                return (m `M.union` x)
            ) empty pat'
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
            ) empty (toList ms')
--        ms <- forM (toList ms') $ \(k,xs) -> do
--            x <- xs
--            return (k,x)
--        let ms' = fromList ms
        guard $ keysSet ms == vars
        return ms
    where
        pat' = L.map f pat
        f (VARIABLE s) = GENERIC s
        f t = rewrite f t
        types' = map as_generic types
        vars = S.unions $ map generics pat'
        ms' = unionsWith (++) ms
--        ms :: [Map String [FOType]]
        ms :: [Map String [Map String FOType]]
        ms = do
            p  <- pat'
            t  <- types'
            m  <- M.maybeToList $ unify p t
            ms <- M.maybeToList $ mapM type_strip_generics (elems m) 
            let ms' = M.fromList $ zip (map (reverse . drop 2 . reverse) $ keys m) ms
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
    with_tracing $ 
--    trace (show types) $
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
        fdm = M.fromJust . var_strip_generics

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
        in
        case g of
            Binder Forall (Var nam t:vs) rs ts -> do
                let (Context ss vars funs defs dums) = ctx
                    v   = Var (fresh nam $ 
                                      keysSet vars 
                            `S.union` keysSet funs
                            `S.union` keysSet defs) t
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
        m = fromList $
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
        s <- verify code (maybe 4 id n)
        case s of
            Right Sat -> return Invalid
            Right Unsat -> return Valid
            Right SatUnknown -> do
                return ValUnknown
            Left xs -> do
                fail $ "discharge: " ++ xs

verify :: [Command] -> Int -> IO (Either String Satisfiability)
verify ys n = do
        let xs = concat $ map reverse $ groupBy eq ys
            !code = (unlines $ map (show . as_tree) xs) -- $ [Push] ++ xs ++ [Pop])
            eq (Assert _) (Assert _) = True
            eq _ _                   = False
        (_,out,err) <- feed_z3 code n
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

