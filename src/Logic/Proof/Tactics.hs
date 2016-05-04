{-# LANGUAGE TypeOperators
    , OverloadedStrings
    , UndecidableInstances   #-}
module Logic.Proof.Tactics 
    ( Tactic, TacticT, get_line_info, get_context
    , get_goal, by_parts
    , is_fresh, get_hypotheses, assert, assume
    , by_cases, easy, new_fresh, free_goal
    , instantiate_hyp, with_line_info
    , runTactic, runTacticT
    , runTacticWithTheorems, runTacticTWithTheorems
    , make_expr, fresh_label
    , last_step, add_step, TheoremRef ( .. )
    , get_dummy, lookup_hypothesis, clear_vars
    , free_vars_goal, instantiate_hyp_with
    , get_named_hyps, get_nameless_hyps
    , get_used_vars, get_allocated_vars
    , use_theorems
    , define
    , by_symmetry
    , indirect_inequality
    , indirect_equality
    )
where

import Logic.Expr hiding ( instantiate )
import Logic.Operator
import Logic.WellDefinedness
import Logic.Proof.ProofTree
import Logic.Proof.Sequent

    -- Libraries
import Control.Arrow
import Control.Lens hiding (Context)
import Control.Precondition

import Control.Monad hiding ( guard )
import Control.Monad.RWS hiding ( guard )
import Control.Monad.Trans.Either

import           Data.Graph hiding (Table)
import           Data.List as L
import qualified Data.List.Ordered as OL
import           Data.Map.Class  as M
import qualified Data.Set  as S
import           Data.Tuple

import Text.Printf.TH

import Utilities.Error
import Utilities.Graph hiding ( map )
import Utilities.Syntactic ( Error (..), LineInfo )
import Utilities.Table

data TacticParam = TacticParam 
    { _sequent :: Sequent
    , _line_info :: LineInfo
    , _theorems  :: Table Label Expr
    }

makeLenses ''TacticParam

newtype TacticT m a = TacticT 
        { unTactic :: ErrorT 
                (RWST 
                    TacticParam 
                    [Label] 
                    (S.Set Label,S.Set Name) m) a }
    deriving (Functor,Applicative,MonadError)

instance Show (TacticT m a) where
  show _ = "<tactic>"

type Tactic = TacticT Identity

tac_local :: Monad m
          => (TacticParam -> TacticParam)
          -> TacticT m a
          -> TacticT m a
tac_local f (TacticT (ErrorT cmd)) = TacticT $ ErrorT $ local f cmd

tac_listen :: Monad m
           => TacticT m a
           -> TacticT m (a, [Label])
tac_listen (TacticT (ErrorT cmd)) = TacticT $ ErrorT $ do
        (x,w) <- listen cmd
        case x of
            Right (x,y) -> return $ Right ((x,w),y)
            Left x -> return $ Left x

tac_censor :: Monad m
           => ([Label] -> [Label])
           -> TacticT m a
           -> TacticT m a
tac_censor f (TacticT (ErrorT cmd)) = TacticT $ ErrorT $ censor f cmd

with_line_info :: Monad m => LineInfo -> TacticT m a -> TacticT m a
with_line_info li (TacticT cmd) = 
        TacticT $ ErrorT $ local (line_info .~ li) $ runErrorT cmd

with_goal :: Monad m => Expr -> TacticT m a -> TacticT m a
with_goal e = tac_local (sequent.goal .~ e)
        -- $ runErrorT cmd

with_hypotheses :: Monad m
                => [(Label, Expr)] 
                -> TacticT m a 
                -> TacticT m a
with_hypotheses es cmd = do
    tac_local (sequent.named %~ (M.fromList es `M.union`)) cmd

with_nameless_hypotheses :: Monad m
                => [Expr] 
                -> TacticT m a 
                -> TacticT m a
with_nameless_hypotheses es cmd = do
    tac_local (sequent.nameless %~ (es++)) cmd

with_variables :: Monad m
               => [Var] -> TacticT m Proof -> TacticT m Proof
with_variables vs (TacticT cmd) = TacticT $ do
    ctx   <- view $ sequent.context
    let clashes = M.intersection
                (M.fromList $ L.map (view name &&& const ()) vs)
                (symbols ctx)
    li <- view line_info
    unless (M.null clashes) $ 
        hard_error [Error ([printf|redefinition of %s|] $ intercalate "," $ L.map render $ keys clashes) 
            $ li]
    ErrorT $ local (sequent.constants %~ (symbol_table vs `M.union`)) $ 
        runErrorT cmd

get_dummy :: Monad m
          => Name -> TacticT m Var
get_dummy var = do
        ctx <- get_context
        li  <- get_line_info
        let Context _ _ _ _ vars = ctx
        maybe 
            (hard_error [Error ("invalid dummy: " ++ render var) li])
            return
            $ M.lookup var vars

get_line_info :: Monad m
              => TacticT m LineInfo
get_line_info = TacticT $ lift $ asks _line_info

get_goal :: Monad m
         => TacticT m Expr
get_goal = TacticT $ do
        view $ sequent.goal

get_named_hyps :: Monad m
               => TacticT m (Table Label Expr)
get_named_hyps = TacticT $ do 
        view $ sequent.named

get_nameless_hyps :: Monad m
                  => TacticT m [Expr]
get_nameless_hyps = TacticT $ do 
        view $ sequent.nameless

get_hypotheses :: Monad m
               => TacticT m [Expr]
get_hypotheses = TacticT $ do
        asm  <- view $ sequent.nameless
        hyps <- view $ sequent.named
        return $ asm ++ elems hyps

lookup_hypothesis :: Monad m
                  => TheoremRef
                  -> TacticT m Expr
lookup_hypothesis (ThmRef hyp inst) = do
        li <- get_line_info
        let err_msg = Error ([printf|predicate is undefined: '%s'|] $ show hyp) li
        hyps <- TacticT $ view $ sequent.named
        x <- maybe 
            (hard_error [err_msg])
            return
            $ M.lookup hyp hyps
        instantiate x inst

get_context :: Monad m
            => TacticT m Context
get_context = TacticT $ do
        view $ sequent.context

add_theorems :: Monad m
             => [(Label,Expr)] 
             -> TacticT m Proof 
             -> TacticT m (Proof, [Label])
add_theorems thms proof = do
        let new_thm = fromList thms
            f xs = sort xs `OL.minus` keys new_thm
        tac_censor f $ tac_listen $ tac_local 
            (theorems %~ (new_thm `M.union`))
            proof
        

assert :: Monad m
       => [(Label,Expr,TacticT m Proof)] 
       -> TacticT m Proof 
       -> TacticT m Proof
assert xs proof = make_hard $ 
        if L.null xs
        then proof
        else do
            li <- get_line_info
            let thm       = L.map f xs
                f (x,y,_) = (x,y)
            ps <- forM xs $ \(lbl,x,m) -> do
                p     <- easy
                (p,r) <- add_theorems thm 
                    $ make_soft p 
                    $ with_goal x m
                return ((lbl,x),(lbl,(x,p)),(L.map (\x -> (lbl,x)) r))
            let (xs,ys,zs) = unzip3 ps
                -- (xs,ys,zs) =
                -- ( new hypotheses
                -- , assertions with proof objects
                -- , dependencies between assertions)
            make_hard $ forM_ (cycles $ concat zs) $ \x ->
                let msg = [printf|a cycle exists between the proofs of the assertions %s|] in
                case x of
                    AcyclicSCC _ -> return ()
                    CyclicSCC cs -> soft_error [Error (msg $ intercalate "," $ L.map show cs) li]
            p  <- with_hypotheses xs proof
            return $ Assertion (fromList ys) (concat zs) p li

assume :: Monad m
       => [(Label,Expr)]
       -> Expr
       -> TacticT m Proof        
       -> TacticT m Proof
assume xs new_g proof = do
        li <- get_line_info
        p  <- with_hypotheses xs
            $ with_goal new_g proof
        return $ Assume (fromList xs) new_g p li

clear_vars :: Monad m
           => [Var]
           -> TacticT m Proof
           -> TacticT m Proof
clear_vars vars proof = do
        param <- TacticT $ lift $ ask
        old_vars <- TacticT $ view $ sequent.constants
        let -- Sequent ctx _ asm hyp g = sequent param
            -- new_asm = L.filter f asm
            -- new_hyp = M.filter f hyp
            f x     = not $ any (`S.member` used_var x) vars
            new_vars = L.foldl (flip M.delete) old_vars (L.map (view name) vars)
        li    <- get_line_info
        tac_local 
            (sequent %~ 
                \s -> s & constants .~ new_vars 
                        & nameless %~ L.filter f
                        & named    %~ M.filter f) $
            do  (lbls,ids)  <- TacticT $ lift $ get
                let new_ids = ids `S.difference` S.fromList (L.map (view name) vars)
                TacticT $ lift $ put (lbls,new_ids)
                (p,w)  <- tac_listen proof
                TacticT $ do
                  lift $ put (lbls,ids)
                  let thm = M.filter f $ _theorems param 
                        `intersection` fromList (zip w $ repeat ())
                  new_ctx <- view $ sequent.context
                  new_asm <- view $ sequent.nameless
                  new_hyp <- view $ sequent.named
                  return $ Keep new_ctx new_asm (thm `M.union` new_hyp) p li
        

by_cases :: Monad m
         => [(Label, Expr, TacticT m Proof)]
         -> TacticT m Proof
by_cases cs = make_hard $ do
        li <- get_line_info
        ps <- forM cs $ \(lbl,e,m) -> do
            p <- easy
            p <- make_soft p $ with_hypotheses [(lbl,e)] m 
            return (lbl,e,p)
        return $ ByCases ps li

by_parts :: Monad m
         => [(Expr, TacticT m Proof)]
         -> TacticT m Proof
by_parts cs = do
        li <- get_line_info
        ps <- forM cs $ \(e,m) -> do
            p <- with_goal e m 
            return (e,p)
        return $ ByParts ps li

easy :: Monad m
     => TacticT m Proof
easy = do
        li <- get_line_info
        return $ Easy li

use_theorems :: Monad m
             => [(TheoremRef,LineInfo)]
             -> TacticT m Proof
             -> TacticT m Proof
use_theorems hint cmd = do
        thms <- derive_theorems hint
        with_hypotheses thms $
            instantiate_all hint cmd

derive_theorems :: Monad m
                => [(TheoremRef,LineInfo)]
                -> TacticT m [(Label, Expr)]
derive_theorems hint = do
        thms     <- TacticT $ view theorems
        thms     <- forM hint $ \ref -> 
            case ref of
                (ThmRef lbl _, _) -> do
                    hyps <- get_named_hyps
                    case lbl `M.lookup` thms of
                        Just e 
                            | not $ lbl `M.member` hyps -> do
                                TacticT $ lift $ tell [lbl]
                                return [(lbl,e)]
                        _ -> return []
                -- (Lemma _, _) -> return []
        return $ concat thms

use_theorems' :: Monad m
              => [(TheoremRef,LineInfo)]
              -> TacticT m a
              -> TacticT m a
use_theorems' hint cmd = do
        thms <- derive_theorems hint
        with_hypotheses thms cmd

add_step :: Monad m
         => Expr
         -> BinOperator
         -> [(TheoremRef,LineInfo)]
         -> TacticT m Calculation
         -> TacticT m Calculation
add_step step op hint calc = make_hard $ do
        use_theorems' hint $ do
            hyp     <- forM hint $ \(ref,li) -> 
                with_line_info li $ make_soft ztrue $ lookup_hypothesis ref
            trivial <- last_step ztrue
            r       <- make_soft trivial calc
            li      <- get_line_info
            return r { 
                first_step = step,
                following  = (op,first_step r,hyp,li):following r }

last_step :: Monad m => Expr -> TacticT m Calculation
last_step xp = do
        li  <- get_line_info
        ctx <- get_context
        return $ Calc ctx ztrue xp [] li

get_used_vars :: Monad m
              => TacticT m [Var]
get_used_vars = do
        es <- TacticT $ view $ sequent.expressions
        return $ S.toList $ S.unions $ L.map used_var es

get_allocated_vars :: Monad m
                   => TacticT m [Name]
get_allocated_vars = do
        (_,ids) <- TacticT $ lift $ get
        return $ S.toList ids

is_fresh :: Monad m
         => Name -> TacticT m Bool
is_fresh v = TacticT $ do
        are_fresh [v] <$> view sequent

new_fresh :: (Monad m, Pre)
          => String
          -> Type 
          -> TacticT m Var
new_fresh name t = do
        fix (\rec n suf -> do
            let v = fromString'' (name ++ suf)
            b <- is_fresh v
            (lbls,ids) <- TacticT $ lift $ get
            if b && not (v `S.member` ids)
            then TacticT $ do
                lift $ put (lbls,S.insert v ids)
                return $ Var v t
            else do
                rec (n+1 :: Int) (show n)
            ) 0 ""

is_label_fresh :: Monad m => Label -> TacticT m Bool
is_label_fresh lbl = TacticT $ do
        hyps <- view $ sequent.named
        thm  <- view theorems
        return $   (not $ lbl `member` hyps) 
                && (not $ lbl `member` thm)

fresh_label :: Monad m
            => String -> TacticT m Label
fresh_label name = do
        fix (\rec n suf -> do
            let v = label (name ++ suf)
            b           <- is_label_fresh v
            (lbls, ids) <- TacticT $ get
            if b && not (v `S.member` lbls) 
            then TacticT $ do
                lift $ put (S.insert v lbls,ids)
                return v
            else do
                rec (n+1 :: Int) (show n)
            ) 0 ""

free_vars_goal :: Monad m
               => [(Name,Name)]
               -> TacticT m Proof
               -> TacticT m Proof
free_vars_goal [] proof = proof
free_vars_goal ((v0,v1):vs) proof = do
        free_goal v0 v1 $
            free_vars_goal vs proof

bind :: Monad m => String -> Maybe a -> TacticT m a
bind _ (Just x)  = return x
bind msg Nothing = fail msg

guard :: Monad m => String -> Bool -> m ()
guard msg b = unless b $ fail msg

define :: Monad m
       => [(Name, Expr)]
       -> TacticT m Proof
       -> TacticT m Proof
define xs proof = do
    let po (v,e) = ("WD" </> label (render v),well_definedness e,easy)
        vars = L.map (uncurry Var . (second type_of)) xs
    li <- get_line_info
    p  <- assert (L.map po xs) $ 
      with_variables vars $
        with_nameless_hypotheses 
          (zipWith zeq (L.map Word vars) (L.map snd xs)) $
          proof
    return $ if L.null xs
      then p
      else Definition (fromList $ zip vars $ L.map snd xs) p li

free_goal :: Monad m
          => Name -> Name
          -> TacticT m Proof 
          -> TacticT m Proof
free_goal v0 v1 m = do
        li    <- get_line_info
        goal  <- get_goal 
        fresh <- is_fresh v1
        (new,t) <- case goal of 
            Binder Forall bv r t _ -> do
                  guard ([printf|'%s' is not a fresh variable|] $ render v1)
                      fresh
                  v0'@(Var _ tt) <- bind 
                      ([printf|'%s' is not a bound variable in:\n%s|]
                                (render v0) $ pretty_print' goal)
                      $ L.lookup v0 (zip bv' bv)
                  return
                      ( rename v0 v1 
                          $ zforall (L.delete v0' bv) r t
                      , tt)
                where
                  bv' = L.map (view name) bv
            _ -> fail $ "goal is not a universal quantification:\n" ++ pretty_print' goal
        p <- with_variables [Var v1 t] $ with_goal new m
        return $ FreeGoal v0 v1 t p li

instantiate :: Monad m
            => Expr -> [(Var,Expr)] 
            -> TacticT m Expr
instantiate hyp ps = do
        case hyp of
            Binder Forall vs r t _
                | all (`elem` vs) (L.map fst ps) -> do
                    let new_vs = L.foldl (flip L.delete) vs (L.map fst ps)
                        ps'    = M.mapKeys (view name) $ fromList ps
                        re     = substitute ps' r
                        te     = substitute ps' t
                        newh   = if L.null new_vs
                                    then zimplies re te
                                    else zforall new_vs re te
                    return newh
            _ 
                | not $ L.null ps -> 
                    fail $ "predicate is not a universal quantification:\n" 
                        ++ pretty_print' hyp
                | otherwise  -> return hyp

instantiate_all :: Monad m
                => [(TheoremRef,LineInfo)]
                -> TacticT m Proof
                -> TacticT m Proof
instantiate_all [] proof = proof
instantiate_all ((ThmRef lbl ps, li):rs) proof = do
        hyps    <- get_named_hyps -- _hypotheses
        new_lbl <- fresh_label $ show lbl
        h <- maybe
            (hard_error [Error ([printf|inexistant hypothesis: %s|] $ show lbl) li])
            return 
            (lbl `M.lookup` hyps)
        instantiate_hyp h new_lbl ps $
            instantiate_all rs proof

instantiate_hyp_with :: Monad m
                     => Expr 
                     -> [[(Var,Expr)]] 
                     -> TacticT m Proof
                     -> TacticT m Proof    
instantiate_hyp_with _ [] proof = proof
instantiate_hyp_with hyp (p:ps) proof = do
        lbl <- fresh_label "H"
        instantiate_hyp hyp lbl p $
            instantiate_hyp_with hyp ps proof

instantiate_hyp :: Monad m
                => Expr -> Label 
                -> [(Var,Expr)] 
                -> TacticT m Proof
                -> TacticT m Proof
instantiate_hyp hyp lbl ps proof = do
        hyps <- get_hypotheses
        li   <- get_line_info
        if hyp `elem` hyps then do
            newh <- instantiate hyp ps
            p    <- with_hypotheses [(lbl,newh)] proof
            return $ InstantiateHyp hyp (fromList ps) p li
        else
            fail $ "formula is not an hypothesis:\n" 
                ++ pretty_print' hyp

make_expr :: Monad m
          => Either [String] a
          -> TacticT m a
make_expr e = do
        li <- get_line_info
        let f xs = Left $ L.map (`Error` li) xs
        TacticT $ fromEitherT $ hoistEither (either f Right e)

runTacticT :: Monad m
           => LineInfo -> Sequent
           -> TacticT m a -> m (Either [Error] a)
runTacticT li s (TacticT tac) = do
        (x,_,_) <- runRWST (runErrorT tac) (TacticParam s li M.empty) (S.empty,S.empty)
        case x of
            Right (x,[])  -> return $ Right x
            Right (_,err) -> return $ Left err
            Left err -> return $ Left err

runTacticTWithTheorems :: Monad m
                       => LineInfo -> Sequent
                       -> Table Label Expr
                       -> TacticT m a -> m (Either [Error] (a,[Label]))
runTacticTWithTheorems li s thms (TacticT tac) = do
        (x,_,thms) <- runRWST (runErrorT tac) (TacticParam s li thms) (S.empty,S.empty)
        case x of
            Right (x,[])  -> return $ Right (x,thms)
            Right (_,err) -> return $ Left err
            Left err -> return $ Left err

runTactic :: LineInfo -> Sequent -> Tactic a -> Either [Error] a
runTactic li s tac = runIdentity (runTacticT li s tac)

runTacticWithTheorems :: LineInfo -> Sequent 
                      -> Table Label Expr
                      -> Tactic a -> Either [Error] (a, [Label])
runTacticWithTheorems li s thms tac = runIdentity (runTacticTWithTheorems li s thms tac)
          
instance Monad m => Monad (TacticT m) where
    TacticT m >>= f = TacticT $ m >>= (unTactic . f)
    return x       = TacticT $ return x
    fail msg       = do
            li <- get_line_info
            TacticT $ hard_error [Error msg li]

instance MonadState s m => MonadState s (TacticT m) where
    get = lift get
    put x = lift $ put x

instance MonadReader r m => MonadReader r (TacticT m) where
    ask = lift $ ask
    local f (TacticT (ErrorT (RWST cmd))) = TacticT $ 
            ErrorT $ 
            RWST $ \r s ->
            local f $ cmd r s

instance MonadTrans TacticT where
    lift cmd = TacticT $ lift $ lift cmd

by_symmetry :: Monad m
            => [Var]
            -> Label
            -> Maybe Label
            -> TacticT m Proof
            -> TacticT m Proof
by_symmetry vs hyp mlbl proof = do
        cs <- lookup_hypothesis (ThmRef hyp [])
        let err0 = [printf|expecting a disjunction\n%s: %s|] (show hyp) $ pretty_print' cs
        lbl  <- maybe (fresh_label "symmetry") return mlbl
        goal <- get_goal
        case cs of
            FunApp f cs
                | view name f /= (z3Name "or") -> fail err0
                | otherwise -> do
                    ps <- forM (permutations vs) $ \us -> do
                        hyp <- get_named_hyps
                        asm <- get_nameless_hyps
                        let rn = zip vs us
                            new_hyp = M.filter p $ M.map f hyp 
                            new_asm = L.filter p $ L.map f asm
                            f h = rename_all rn h
                            p h = any (`S.member` used_var h) vs
                        new_asm <- forM new_asm $ \x -> do
                            lbl <- fresh_label "H"
                            return (x,lbl)
                        return $ M.fromList $ L.map swap (toList new_hyp) ++ new_asm
                    let common = (head cs,hyp) : M.toList (intersections ps)
                        named  = L.map swap common
                        thm = zforall vs (zall $ L.map fst common) goal
                        f xs = zip vs $ L.map Word xs
                    cs <- forM cs $ \x -> return (hyp,x,easy)
                    assert [(lbl,thm,clear_vars vs $ do
                            us <- forM vs $ \(Var n t) -> new_fresh (render n) t
                            free_vars_goal (zip (L.map (view name) vs) 
                                                (L.map (view name) us)) 
                              $ assume named goal proof)] $
                        instantiate_hyp_with thm (L.map f $ permutations vs) $ 
                            by_cases cs
            _ -> fail err0

indirect_inequality :: Monad m
                    => Either () () 
                    -> BinOperator 
                    -> Var
                    -> TacticT m Proof
                    -> TacticT m Proof
indirect_inequality dir op zVar@(Var _ t) proof = do 
        x_decl <- new_fresh "x" t
        y_decl <- new_fresh "y" t
        z_decl <- new_fresh "z" t
        let x         = Word x_decl
            y         = Word y_decl
            z         = Word z_decl
            rel       = mk_expr op
            rel_z x y = case dir of
                        Left ()  -> rel z x `mzimplies` rel z y
                        Right () -> rel y z `mzimplies` rel x z
            thm_rhs x y = mzforall [z_decl] mztrue $ rel_z x y
        thm  <- make_expr $ mzforall [x_decl,y_decl] mztrue $ rel x y `mzeq` thm_rhs x y
        goal <- get_goal
        let is_op f x y = either (const False) id $ do
                            xp <- mk_expr op x y
                            return $ FunApp f [x,y] == xp
        case goal of
            FunApp f [lhs,rhs] 
                | is_op f x y -> do
                    new_goal <- make_expr $ mzforall [z_decl] mztrue $ thm_rhs lhs rhs
                    g_lbl   <- fresh_label "new:goal"
                    thm_lbl <- fresh_label "indirect:ineq"
                    assert 
                        [ (thm_lbl, thm, easy)       -- (Ax,y:: x = y == ...)
                        , (g_lbl, new_goal, do       -- (Az:: z ≤ lhs => z ≤ rhs)
                                free_goal (view name z_decl) (view name zVar) proof) ]
                        $ do
                            lbl <- fresh_label "inst"
                            instantiate_hyp
                                thm lbl                             -- | we could instantiate indirect
                                [ (x_decl,lhs)                      -- | inequality explicitly 
                                , (y_decl,rhs) ]                    -- | for that, we need hypotheses 
                                easy                                -- | to be named in sequents
                                                              
            _ -> fail $ "expecting an inequality:\n" ++ pretty_print' goal

indirect_equality :: Monad m
                  => Either () () 
                  -> BinOperator 
                  -> Var
                  -> TacticT m Proof
                  -> TacticT m Proof
indirect_equality dir op zVar@(Var _ t) proof = do 
        x_decl <- new_fresh "x" t
        y_decl <- new_fresh "y" t
        z_decl <- new_fresh "z" t
        let x       = Word x_decl
            y       = Word y_decl
            z       = Word z_decl
            rel     = mk_expr op
            rel_z   = case dir of
                        Left ()  -> rel z
                        Right () -> flip rel z
            thm_rhs x y = mzforall [z_decl] mztrue $ rel_z x `mzeq` rel_z y
        thm  <- make_expr $ mzforall [x_decl,y_decl] mztrue $ Right (zeq x y) `mzeq` thm_rhs x y
        goal <- get_goal
        case goal of
            FunApp f [lhs,rhs] 
                | view name f == z3Name "=" -> do
                    new_goal <- make_expr $ mzforall [z_decl] mztrue $ thm_rhs lhs rhs
                    assert 
                        [ (label "indirect:eq", thm, easy)      -- (Ax,y:: x = y == ...)
                        , (label "new:goal", new_goal, do       -- (Az:: z ≤ lhs == z ≤ rhs)
                                free_goal (view name z_decl) (view name zVar) proof) ]
                        $ do
                            lbl <- fresh_label "inst"
                            instantiate_hyp                       
                                thm lbl                             -- | we could instantiate indirect
                                [ (x_decl,lhs)                      -- | inequality explicitly 
                                , (y_decl,rhs) ]                    -- | for that, we need hypotheses 
                                easy                                -- | to be named in sequents
                                                              
            _ -> fail $ "expecting an equality:\n" ++ pretty_print' goal

intersectionsWith :: Ord a => (b -> b -> b) -> [Map a b] -> Map a b
intersectionsWith _ [] = error "intersection of an empty list of sets"
intersectionsWith f (x:xs) = L.foldl (intersectionWith f) x xs

intersections :: Ord a => [Map a b] -> Map a b
intersections = intersectionsWith const

--by_antisymmetry :: Monad m 
--                => BinOperator 
--                -> 
