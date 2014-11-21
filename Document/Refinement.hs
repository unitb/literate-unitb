{-# LANGUAGE FlexibleInstances, FlexibleContexts        #-}
{-# LANGUAGE DeriveDataTypeable, IncoherentInstances    #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables     #-}
{-# LANGUAGE BangPatterns                               #-}
module Document.Refinement where

    -- Module
import Document.Visitor
import Document.Proof

import UnitB.AST
import UnitB.PO
import UnitB.POGenerator as POG

import Latex.Parser

import Logic.Expr

    -- Libraries
import Control.DeepSeq

import Control.Monad.Trans.Either
import Control.Monad.RWS as RWS

import Data.Char
import Data.List as L ( intercalate, (\\), null )
import Data.Map as M hiding ( map, (\\) )
import Data.Maybe
import Data.Set as S hiding ( fromList, member, map, (\\) )
import Data.Typeable

import Utilities.Format
import Utilities.Syntactic

add_proof_edge :: MonadState System m 
               => Label -> [Label] -> m ()
add_proof_edge x xs = do
        RWS.modify (\x -> x { proof_struct = edges ++ proof_struct x } )
    where
        edges = zip (repeat x) xs

data RuleParserParameter = 
    RuleParserParameter
        Machine 
        (Map Label ProgressProp)
        (Map Label SafetyProp)
        Label
        [Label]
        [LatexDoc]

data Add = Add
    deriving (Eq,Typeable,Show)

instance RefRule Add where
    rule_name _       = label "add"
    refinement_po _ m = assert m "" zfalse

instance NFData Add where

type ERWS = EitherT [Error] (RWS LineInfo [Error] System)

class RuleParser a where
    parse_rule :: a -> [Label] -> String 
               -> RuleParserParameter 
               -> ERWS Rule

instance RefRule a => RuleParser (ERWS a,()) where
    parse_rule (cmd,_) [] _ _ = do 
            x <- cmd
            return $ Rule x
    parse_rule _ hyps_lbls _ _ = do
        li <- lift $ ask
        left [Error (format "too many hypotheses in the application of the rule: {0}" 
                          $ intercalate "," $ map show hyps_lbls) li]

instance RefRule a => RuleParser (a,()) where
    parse_rule (x,()) xs y z = do
            let cmd = return x :: ERWS a
            parse_rule (cmd,()) xs y z

instance RuleParser (a,()) => RuleParser (ProgressProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter _ prog _ _ _ _) = do
        case M.lookup x prog of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a progress property" rule x) li]
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RuleParser (a,()) => RuleParser (SafetyProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter _ _ saf _ _ _) = do
        case M.lookup x saf of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a safety property" rule x) li]
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RuleParser (a,()) => RuleParser (Transient -> a,()) where
    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter m _ _ _ _ _) = do
        case M.lookup x $ transient $ props m of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a transient predicate" rule x) li]
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RefRule a => RuleParser ([Label] -> [Event] -> ERWS a, ()) where
    parse_rule (f,_) es rule (RuleParserParameter m _ _ _ _ _) = do
        -- evts <- bind_all x
        evts <- bind_all es 
            (format "event {0} is undeclared") 
            (`M.lookup` events m)
        -- let (es,ys) = span (`M.member` events m) xs
            -- evts = map (events m !) es
        li <- lift $ ask
        when (L.null es) 
            $ left [Error (format "refinement ({0}): at least one event is required" rule) li]
        rule <- f es evts
        return (Rule rule) -- ys rule param


--instance RuleParser (a,()) => RuleParser (Schedule -> a,()) where
--    parse_rule (f,_) (x:xs) rule param@(RuleParserParameter m _ _ _ _ _) = do
--        case M.lookup x $ schedule $ props m of
--            Just p -> parse_rule (f p, ()) xs rule param
--            Nothing -> do
--                li <- lift $ ask
--                left [Error (format "refinement ({0}): {1} should be a schedule" rule x) li]
--    parse_rule _ [] rule _ = do
--                li <- lift $ ask
--                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RefRule a => RuleParser ([ProgressProp] -> a,()) where
    parse_rule (f,_) xs rule (RuleParserParameter _ prog _ _ _ _) = do
            xs <- forM xs g
            return $ Rule (f xs)        
        where
            g x = maybe (do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a progress property" rule x) li] )
                return
                $ M.lookup x prog

instance RefRule a => RuleParser ([SafetyProp] -> a,()) where
    parse_rule (f,_) xs rule (RuleParserParameter _ _ saf _ _ _) = do
            xs <- forM xs g
            return $ Rule (f xs)        
        where
            g x = maybe (do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a safety property" rule x) li] )
                return
                $ M.lookup x saf


parse :: RuleParser a
      => a -> String -> RuleParserParameter
      -> EitherT [Error] (RWS LineInfo [Error] System) Rule
parse rc n param@(RuleParserParameter _ _ _ goal_lbl hyps_lbls _) = do
        add_proof_edge goal_lbl hyps_lbls
        parse_rule rc (goal_lbl:hyps_lbls) n param

assert :: Machine -> String -> Expr -> POGen ()
assert m suff prop = assert_hyp m suff M.empty M.empty prop

assert_hyp :: Machine -> String 
           -> Map String Var -> Map Label Expr
           -> Expr -> POGen () 
assert_hyp m suff cnst hyps prop = 
    with (do
            POG.context $ assert_ctx m
            POG.context $ step_ctx m
            POG.context $ ctx
            named_hyps $ invariants m
            named_hyps hyps )
        $ emit_goal [po_lbl] prop
    where
        ctx = Context M.empty cnst M.empty M.empty M.empty
        po_lbl 
            | L.null suff = composite_label []
            | otherwise   = composite_label [label suff]

data Ensure = Ensure ProgressProp [Label] [Event] TrHint
    deriving (Eq,Typeable,Show)

instance RefRule Ensure where
    rule_name _ = "ensure"
    refinement_po (Ensure (LeadsTo vs p q) lbls _ hint) m = do
            prop_saf m ("", Unless vs p q Nothing)
            prop_tr m ("", Transient (symbol_table vs) 
                                             (p `zand` znot q) lbls 
                                             hint )

instance NFData Ensure where
    rnf (Ensure x0 x1 x2 x3) = rnf (x0,x1,x2,x3)

data Discharge = Discharge ProgressProp Transient (Maybe SafetyProp)
    deriving (Eq,Typeable,Show)

instance RefRule Discharge where
    rule_name _ = label "discharge"
    refinement_po 
            (Discharge _ _
                (Just (Unless _ _ _ (Just _)))) _
            = error "Discharge.refinement_po: should not reach this point" 
    refinement_po 
            (Discharge 
                    (LeadsTo fv0 p0 q0)
                    (Transient fv1 p1 _ _)
                    (Just (Unless fv2 p2 q2 Nothing))) 
        m = do
            assert m "saf/lhs" (
                zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                        p0 `zimplies` p2
                        ) )
            assert m "saf/rhs" (
                zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                        q2 `zimplies` q0
                        ) )
            assert m "tr" (
                zforall (fv0 ++ M.elems fv1 ++ fv2) ztrue (
                        zand p0 (znot q0) `zimplies` p1
                        ) )
    refinement_po 
            (Discharge 
                    (LeadsTo fv0 p0 q0)
                    (Transient fv1 p1 _ _)
                    Nothing)
            m = do
                assert m "tr/lhs" (
                    zforall (fv0 ++ M.elems fv1) ztrue (
                             (p0 `zimplies` p1) ) )
                assert m "tr/rhs" (
                    zforall (fv0 ++ M.elems fv1) ztrue (
                             (znot p1 `zimplies` q0) ) )

instance NFData Discharge where
    rnf (Discharge p t u) = rnf (p,t,u)

mk_discharge :: ProgressProp -> Transient -> [SafetyProp] -> Discharge
mk_discharge p tr [s] = Discharge p tr $ Just s
mk_discharge p tr []  = Discharge p tr Nothing
mk_discharge _ _ _    = error "expecting at most one safety property" 

parse_discharge :: String -> RuleParserParameter
                -> EitherT [Error] (RWS LineInfo [Error] System) Rule
parse_discharge rule params@(RuleParserParameter _ _ _ goal_lbl hyps_lbls _) = do
    li <- lift $ ask
    when (1 > length hyps_lbls || length hyps_lbls > 2)
        $ left [Error (format "too many hypotheses in the application of the rule: {0}" 
                            $ intercalate "," $ map show hyps_lbls) li]
    add_proof_edge goal_lbl hyps_lbls
    parse (mk_discharge,()) rule params

data Monotonicity = Monotonicity ProgressProp ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Monotonicity where
    rule_name _   = label "monotonicity"
    refinement_po (Monotonicity 
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1))
                  m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                             (p0 `zimplies` p1))
                assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                             (q1 `zimplies` q0))

instance NFData Monotonicity where
    rnf (Monotonicity p q) = rnf (p,q)

data Implication = Implication ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Implication where
    rule_name _   = label "implication"
    refinement_po (Implication 
                    (LeadsTo fv1 p1 q1))
                  m = 
                assert m "" (
                    zforall fv1 ztrue $
                             (p1 `zimplies` q1))

instance NFData Implication where
    rnf (Implication p) = rnf p

data Disjunction = Disjunction ProgressProp [([Var], ProgressProp)]
    deriving (Eq,Typeable,Show)

instance RefRule Disjunction where
    rule_name _ = label "disjunction"
    refinement_po (Disjunction 
                    (LeadsTo fv0 p0 q0)
                    ps) m = do
                assert m "lhs" (
                    zforall fv0 ztrue (
                        ( p0 `zimplies` zsome (map disj_p ps) ) ) )
                assert m "rhs" (
                    zforall fv0 ztrue (
                        ( zsome (map disj_q ps) `zimplies` q0 ) ) )
        where
            disj_p ([], LeadsTo _ p1 _) = p1
            disj_p (vs, LeadsTo _ p1 _) = zexists vs ztrue p1
            disj_q ([], LeadsTo _ _ q1) = q1
            disj_q (vs, LeadsTo _ _ q1) = zexists vs ztrue q1

instance NFData Disjunction where
    rnf (Disjunction p xs) = rnf (p,xs)

disjunction :: ProgressProp -> [ProgressProp] -> Disjunction
disjunction pr0@(LeadsTo fv0 _ _) ps = 
        let f pr1@(LeadsTo fv1 _ _) = (fv1 \\ fv0, pr1)
            ps0 = map f ps
        in (Disjunction pr0 ps0)

data NegateDisjunct = NegateDisjunct ProgressProp ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule NegateDisjunct where
    rule_name _   = label "trading"
    refinement_po 
            (NegateDisjunct
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1))
            m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                                (zand p0 (znot q0) `zimplies` p1))
                assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                                (q1 `zimplies` q0))

instance NFData NegateDisjunct where
    rnf (NegateDisjunct p q) = rnf (p,q)

data Transitivity = Transitivity ProgressProp ProgressProp ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Transitivity where
    rule_name _ = label "transitivity"
    refinement_po 
            (Transitivity
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1)
                    (LeadsTo fv2 p2 q2))
            m = do
                assert m "lhs" ( 
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            p0 `zimplies` p1 )
                assert m "mhs" ( 
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            q1 `zimplies` p2 )
                assert m "rhs" ( 
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            q2 `zimplies` q0 )

instance NFData Transitivity where
    rnf (Transitivity p q r) = rnf (p,q,r)

data PSP = PSP ProgressProp ProgressProp SafetyProp
    deriving (Eq,Typeable,Show)

instance RefRule PSP where
    rule_name _ = label "PSP"
    refinement_po 
            (PSP
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1)
                    (Unless fv2 r b Nothing))
            m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                        (zand p1 r `zimplies` p0))
                assert m "rhs" (
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            (q0 `zimplies` zor (q1 `zand` r) b))
    refinement_po (PSP _ _ (Unless _ _ _ (Just _))) _ 
        = error "PSP.refinement_po: invalid"

instance NFData PSP where
    rnf (PSP p q r) = rnf (p,q,r)

data Induction = Induction ProgressProp ProgressProp Variant
    deriving (Eq,Typeable,Show)

instance RefRule Induction where
    rule_name _ = label "induction"
    refinement_po 
            (Induction 
                    (LeadsTo fv0 p0 q0)
                    (LeadsTo fv1 p1 q1) v)
            m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                        ((p0 `zand` variant_equals_dummy v `zand` variant_bounded v) `zimplies` p1)
                        )
                assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                        (q1 `zimplies` zor (p0 `zand` variant_decreased v `zand` variant_bounded v) q0)
                        )

instance NFData Induction where
    rnf (Induction p q v) = rnf (p,q,v)

parse_induction :: (Monad m)
                => String -> RuleParserParameter
                -> EitherT [Error] (RWST LineInfo [Error] System m) Rule
parse_induction rule (RuleParserParameter m prog _ goal_lbl hyps_lbls hint) = do
        li <- ask
        toEither $ error_list
            [   ( length hyps_lbls /= 1
                , format "too many hypotheses in the application of the rule: {0}" 
                    $ intercalate "," $ map show hyps_lbls)
            ]
        let h0 = head hyps_lbls
        toEither $ error_list
            [   ( not (goal_lbl `member` prog)
                , format "refinement ({0}): {1} should be a progress property" rule goal_lbl )
            ,   ( not (h0 `member` prog)
                , format "refinement ({0}): {1} should be a progress property" rule h0 )
            ]
        let pr0@(LeadsTo fv0 _ _) = prog ! goal_lbl
            pr1@(LeadsTo fv1 _ _) = prog ! h0
        (dir,var,bound) <- case find_cmd_arg 3 ["\\var"] hint of
            Just (_,_,[var,dir,bound],_) -> do
                    var   <- get_expr_with_ctx m 
                            (Context M.empty (symbol_table fv0) M.empty M.empty M.empty)
                            var
                    bound <- get_expr m WithFreeDummies bound
                    dir  <- case map toLower $ concatMap flatten dir of
                        "up"   -> return Up
                        "down" -> return Down
                        _      -> left [Error "expecting a direction for the variant" li]
                    var <- hoistEither $ either
                        (\x -> Left [Error x li]) 
                        Right
                        $ (zcast int)
                        $ Right var
                    bound <- hoistEither $ either
                        (\x -> Left [Error x li])
                        Right
                        $ zcast int
                        $ Right bound
                    return (dir,var,bound)
            Nothing -> left [Error "expecting a variant" li]
            _ -> left [Error "invalid variant" li]
        dum <- case fv1 \\ fv0 of
            [v] -> return v
            _   -> left [Error (   "inductive formula should have one free "
                                ++ "variable to record the variant") li]                    
        add_proof_edge goal_lbl [h0]
        return $ Rule (Induction pr0 pr1 (IntegerVariant dum var bound dir))

instance RefRule ScheduleChange where 
    rule_name     r = 
        case rule r of 
            Replace _ _      -> label "delay"
            Weaken           -> label "weaken"
            ReplaceFineSch _ _ _ _ -> label "replace"
            RemoveGuard _          -> label "grd"
            AddGuard _             -> label "add"
    refinement_po r m = 
        case rule r of
            Replace (_,prog) (_,saf) ->
                let LeadsTo vs p0 q0  = prog
                    Unless us p1 q1 _ = saf
                in do
                    assert m "prog/lhs" (
                        zforall (vs ++ ind) ztrue $
                            zall (old_c ++ old_f) `zimplies` p0
                            )
                    assert m "prog/rhs" (
                        zforall (vs ++ ind) ztrue $
                            q0 `zimplies` new_part
                            )
                    assert m "saf/lhs" (
                        zforall (us ++ ind) ztrue $
                            p1 `zeq` new_part
                            )
                    assert m "saf/rhs" (
                        zforall (us ++ ind) ztrue $
                            q1 `zimplies` znot (zall $ old_c ++ old_f)
                            )
            Weaken -> 
                assert m "" $
                    zforall ind ztrue $ zall (old_f ++ old_c) `zimplies` new_part
            ReplaceFineSch _ _ _ lt -> 
                do  case lt of
                        Just (_,prog) -> do
                            let LeadsTo vs p0 q0 = prog
                            assert m "prog/lhs" (
                                zforall (vs ++ ind) ztrue $
                                    zall (old_c ++ old_f) `zimplies` p0
                                    )
                            assert m "prog/rhs" (
                                zforall (vs ++ ind) ztrue $
                                    q0 `zimplies` new_part
                                    )
                        Nothing -> do
                            assert m "prog/leadsto" (
                                zforall ind ztrue $
                                    zall (old_c ++ old_f) `zimplies` new_part
                                    )
                    assert m "str" (
                        zforall ind ztrue $
                            zall (new_c ++ new_f) `zimplies` old_part
                            )

            RemoveGuard lbl -> 
                    assert_hyp m "" param (new_guard evt) $ old_guard evt ! lbl 
            AddGuard _ -> return ()
        where
            param = params evt `M.union` indices evt
            new_c = M.elems $ coarse $ new_sched evt
            old_c = M.elems $ coarse $ old_sched evt
            new_f = map snd $ maybeToList $ fine $ new_sched evt
            old_f = map snd $ maybeToList $ fine $ old_sched evt
            sch  =  scheds evt
            evt = events m ! event r
            ind = M.elems $ indices evt 
            old_part = zall $ map (sch!) $ S.elems $ remove r `S.union` keep r
            new_part = zall $ map (sch!) $ S.elems $ add r `S.union` keep r
--    refinement_po (n, r@(Weaken lbl _ _))    m = 
--            
--        where
--            sch  =  c_sched evt
--            evt = events m ! lbl
--            ind = M.elems $ indices evt
--            sch0 = zall $ map (sch!) $ S.elems $ remove r `S.union` keep r
--            sch1 = zall $ map (sch!) $ S.elems $ add r `S.union` keep r

--data Cancellation = Cancellation ProgressProp ProgressProp ProgressProp
--
--instance RefRule Cancellation where
--    rule_name _ = label "cancellation"
--    refinement_po 
--        (   Cancellation 
--                    (LeadsTo fv0 p0 q0)
--                    (LeadsTo fv1 p1 q1)
--                    (LeadsTo fv2 p2 q2))
--        m = fromList (
--            assert m "p" (p0 `zimplies` p1)
--         ++ assert m "q" (q1 `zimplies` 
--         ++ assert m "r"
--         ++ assert m "b"
