{-# LANGUAGE FlexibleInstances, FlexibleContexts        #-}
{-# LANGUAGE DeriveDataTypeable, IncoherentInstances    #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables     #-}
{-# LANGUAGE BangPatterns                               #-}
module Document.Refinement where

    -- Module
import Document.Phase
import Document.Proof
import Document.Visitor

import UnitB.AST
import UnitB.PO
import UnitB.POGenerator as POG

import Latex.Parser

import Logic.Expr

    -- Libraries
import Control.Arrow (second)
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
    | RuleParserDecl 
        Phase2
        MachineId
        (Map Label ProgressProp)
        (Map Label SafetyProp)
        (Map Label Transient)
        Label
        [Label]
        [LatexDoc]
        ParserSetting

data Add = Add
    deriving (Eq,Typeable,Show)

instance RefRule Add where
    rule_name _       = label "add"
    refinement_po _ m = assert m "" zfalse
    hyps_labels _     = []
    supporting_evts _ = []

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

getProgress :: RuleParserParameter -> Map Label ProgressProp
getProgress (RuleParserParameter _ prog _ _ _ _) = prog
getProgress (RuleParserDecl _ _ prog _ _ _ _ _ _) = prog

getSafety :: RuleParserParameter -> Map Label SafetyProp
getSafety (RuleParserParameter _ _ saf _ _ _) = saf
getSafety (RuleParserDecl _ _ _ saf _ _ _ _ _) = saf

getTransient :: RuleParserParameter -> Map Label Transient
getTransient (RuleParserParameter m _ _ _ _ _) = transient $ props m
getTransient (RuleParserDecl _ _ _ _ tr _ _ _ _) = tr

getGoal :: RuleParserParameter -> Label
getGoal (RuleParserParameter _ _ _ goal_lbl _ _) = goal_lbl
getGoal (RuleParserDecl _ _ _ _ _ goal_lbl _ _ _) = goal_lbl

getHypotheses :: RuleParserParameter -> [Label]
getHypotheses (RuleParserParameter _ _ _ _ hyps_lbls _) = hyps_lbls
getHypotheses (RuleParserDecl _ _ _ _ _ _ hyps_lbls _ _) = hyps_lbls

getHint :: RuleParserParameter -> [LatexDoc]
getHint (RuleParserParameter _ _ _ _ _ hint) = hint
getHint (RuleParserDecl _ _ _ _ _ _ _ hint _) = hint

getParser :: RuleParserParameter -> ParserSetting
getParser (RuleParserParameter m _ _ _ _ _) = machine_setting m
getParser (RuleParserDecl _ _ _ _ _ _ _ _ parser) = parser

instance RuleParser (a,()) => RuleParser (ProgressProp -> a,()) where
    parse_rule (f,_) xs rule param = do
        let f' x = f
                where
                    _ = x :: Label
        parse_rule (f',()) xs rule param 

instance RuleParser (a,()) => RuleParser (Label -> ProgressProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param = do
        let prog = getProgress param
        case M.lookup x prog of
            Just p -> parse_rule (f x p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a progress property" rule x) li]
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RuleParser (a,()) => RuleParser (SafetyProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param = do
        let saf = getSafety param
        case M.lookup x saf of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a safety property" rule x) li]
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RuleParser (a,()) => RuleParser (Label -> Transient -> a,()) where
    parse_rule (f,_) (x:xs) rule param = do
        let tr = getTransient param
        case M.lookup x tr of
            Just p -> parse_rule (f x p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a transient predicate" rule x) li]
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                left [Error (format "refinement ({0}): expecting more properties" rule) li]

instance RefRule a => RuleParser ([Label] -> ERWS a, ()) where
    parse_rule (f,_) es rule _ = do
        -- evts <- bind_all x
        li <- lift $ ask
        when (L.null es) 
            $ left [Error (format "refinement ({0}): at least one event is required" rule) li]
        rule <- f es
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

instance RefRule a => RuleParser ([(Label,ProgressProp)] -> a,()) where
    parse_rule (f,_) xs rule param = do
            ps <- forM xs g
            return $ Rule (f $ zip xs ps)        
        where
            prog = getProgress param
            g x = maybe (do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a progress property" rule x) li] )
                return
                $ M.lookup x prog

instance RefRule a => RuleParser ([SafetyProp] -> a,()) where
    parse_rule (f,_) xs rule param = do
            xs <- forM xs g
            return $ Rule (f xs)        
        where
            saf = getSafety param
            g x = maybe (do
                li <- lift $ ask
                left [Error (format "refinement ({0}): {1} should be a safety property" rule x) li] )
                return
                $ M.lookup x saf


parse :: RuleParser a
      => a -> String -> RuleParserParameter
      -> EitherT [Error] (RWS LineInfo [Error] System) Rule
parse rc n param = do
        let goal_lbl = getGoal param
            hyps_lbls = getHypotheses param
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

data Ensure = Ensure ProgressProp [Label] TrHint
    deriving (Eq,Typeable,Show)

instance RefRule Ensure where
    rule_name _ = "ensure"
    refinement_po (Ensure (LeadsTo vs p q) lbls hint) m = do
            prop_saf m ("", Unless vs p q Nothing)
            prop_tr m ("", Transient (symbol_table vs) 
                                             (p `zand` znot q) lbls 
                                             hint )
    hyps_labels _ = []
    supporting_evts (Ensure _ hyps _) = map EventId hyps

instance NFData Ensure where
    rnf (Ensure x0 x1 x2) = rnf (x0,x1,x2)

data Discharge = Discharge ProgressProp Label Transient (Maybe SafetyProp)
    deriving (Eq,Typeable,Show)

instance RefRule Discharge where
    rule_name _ = label "discharge"
    hyps_labels (Discharge _ lbl _ _) = [PId lbl]
    supporting_evts (Discharge _ _ (Transient _ _ evts _hint) _) = map EventId evts
        -- where
        --     TrHint _ ev = hint
            -- _ = _ ev
    refinement_po 
            (Discharge _ _ _
                (Just (Unless _ _ _ (Just _)))) _
            = error "Discharge.refinement_po: should not reach this point" 
    refinement_po 
            (Discharge 
                    (LeadsTo fv0 p0 q0)
                    _ (Transient fv1 p1 _ _)
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
                    _ (Transient fv1 p1 _ _)
                    Nothing)
            m = do
                assert m "tr/lhs" (
                    zforall (fv0 ++ M.elems fv1) ztrue (
                             (p0 `zimplies` p1) ) )
                assert m "tr/rhs" (
                    zforall (fv0 ++ M.elems fv1) ztrue (
                             (znot p1 `zimplies` q0) ) )

instance NFData Discharge where
    rnf (Discharge p lbl t u) = rnf (p,lbl,t,u)

mk_discharge :: ProgressProp -> Label -> Transient -> [SafetyProp] -> Discharge
mk_discharge p lbl tr [s] = Discharge p lbl tr $ Just s
mk_discharge p lbl tr []  = Discharge p lbl tr Nothing
mk_discharge _ _ _ _  = error "expecting at most one safety property" 

parse_discharge :: String -> RuleParserParameter
                -> EitherT [Error] (RWS LineInfo [Error] System) Rule
parse_discharge rule params = do
    let goal_lbl = getGoal params
        hyps_lbls = getHypotheses params
    li <- lift $ ask
    when (1 > length hyps_lbls || length hyps_lbls > 2)
        $ left [Error (format "too many hypotheses in the application of the rule: {0}" 
                            $ intercalate "," $ map show hyps_lbls) li]
    add_proof_edge goal_lbl hyps_lbls
    parse (mk_discharge,()) rule params

data Monotonicity = Monotonicity ProgressProp Label ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Monotonicity where
    rule_name _   = label "monotonicity"
    hyps_labels (Monotonicity _ lbl _) = [PId lbl]
    supporting_evts _ = []
    refinement_po (Monotonicity 
                    (LeadsTo fv0 p0 q0)
                    _ (LeadsTo fv1 p1 q1))
                  m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                             (p0 `zimplies` p1))
                assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                             (q1 `zimplies` q0))

instance NFData Monotonicity where
    rnf (Monotonicity p lbl q) = rnf (p,lbl,q)

data Implication = Implication ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Implication where
    rule_name _   = label "implication"
    hyps_labels _ = []
    refinement_po (Implication 
                    (LeadsTo fv1 p1 q1))
                  m = 
                assert m "" (
                    zforall fv1 ztrue $
                             (p1 `zimplies` q1))
    supporting_evts _ = []

instance NFData Implication where
    rnf (Implication p) = rnf p

data Disjunction = Disjunction ProgressProp [(Label,([Var], ProgressProp))]
    deriving (Eq,Typeable,Show)

instance RefRule Disjunction where
    rule_name _ = label "disjunction"
    hyps_labels (Disjunction _ xs) = map (PId . fst) xs
    supporting_evts _ = []
    refinement_po (Disjunction 
                    (LeadsTo fv0 p0 q0)
                    ps') m = do
                assert m "lhs" (
                    zforall fv0 ztrue (
                        ( p0 `zimplies` zsome (map disj_p ps) ) ) )
                assert m "rhs" (
                    zforall fv0 ztrue (
                        ( zsome (map disj_q ps) `zimplies` q0 ) ) )
        where
            ps = map snd ps'
            disj_p ([], LeadsTo _ p1 _) = p1
            disj_p (vs, LeadsTo _ p1 _) = zexists vs ztrue p1
            disj_q ([], LeadsTo _ _ q1) = q1
            disj_q (vs, LeadsTo _ _ q1) = zexists vs ztrue q1

instance NFData Disjunction where
    rnf (Disjunction p xs) = rnf (p,xs)

disjunction :: ProgressProp -> [(Label,ProgressProp)] -> Disjunction
disjunction pr0@(LeadsTo fv0 _ _) ps = 
        let f pr1@(LeadsTo fv1 _ _) = (fv1 \\ fv0, pr1)
            ps0 = map (second f) ps
        in (Disjunction pr0 ps0)

data NegateDisjunct = NegateDisjunct ProgressProp Label ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule NegateDisjunct where
    rule_name _   = label "trading"
    hyps_labels (NegateDisjunct _ lbl _) = [PId lbl]
    supporting_evts _ = []
    refinement_po 
            (NegateDisjunct
                    (LeadsTo fv0 p0 q0) _
                    (LeadsTo fv1 p1 q1) )
            m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1) ztrue $
                                (zand p0 (znot q0) `zimplies` p1))
                assert m "rhs" (
                    zforall (fv0 ++ fv1) ztrue $
                                (q1 `zimplies` q0))

instance NFData NegateDisjunct where
    rnf (NegateDisjunct p lbl q) = rnf (p,lbl,q)

data Transitivity = Transitivity ProgressProp Label ProgressProp Label ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Transitivity where
    rule_name _ = label "transitivity"
    hyps_labels (Transitivity _ l0 _ l1 _) = map PId [l0,l1]
    supporting_evts _ = []
    refinement_po 
            (Transitivity
                    (LeadsTo fv0 p0 q0)
                    _ (LeadsTo fv1 p1 q1)
                    _ (LeadsTo fv2 p2 q2))
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
    rnf (Transitivity p l0 q l1 r) = rnf (p,l0,q,l1,r)

data PSP = PSP ProgressProp Label ProgressProp SafetyProp
    deriving (Eq,Typeable,Show)

instance RefRule PSP where
    rule_name _ = label "PSP"
    hyps_labels (PSP _ lbl _ _) = [PId lbl]
    supporting_evts _ = []
    refinement_po 
            (PSP
                    (LeadsTo fv0 p0 q0)
                    _ (LeadsTo fv1 p1 q1)
                    (Unless fv2 r b Nothing))
            m = do
                assert m "lhs" (
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                        (zand p1 r `zimplies` p0))
                assert m "rhs" (
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            (q0 `zimplies` zor (q1 `zand` r) b))
    refinement_po (PSP _ _ _ (Unless _ _ _ (Just _))) _ 
        = error "PSP.refinement_po: invalid"

instance NFData PSP where
    rnf (PSP p lbl q r) = rnf (p,lbl,q,r)

data Induction = Induction ProgressProp Label ProgressProp Variant
    deriving (Eq,Typeable,Show)

instance RefRule Induction where
    rule_name _ = label "induction"
    hyps_labels (Induction _ lbl _ _) = [PId lbl]
    supporting_evts _ = []
    refinement_po 
            (Induction 
                    (LeadsTo fv0 p0 q0)
                    _ (LeadsTo fv1 p1 q1) v)
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
    rnf (Induction p lbl q v) = rnf (p,lbl,q,v)

parse_induction :: (Monad m)
                => String -> RuleParserParameter
                -> EitherT [Error] (RWST LineInfo [Error] System m) Rule
parse_induction rule param = do
        let prog = getProgress param
            goal_lbl = getGoal param
            hyps_lbls = getHypotheses param
            hint = getHint param
            parser = getParser param
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
            Just (_,_,[var,dir,bound],_) -> toEither $ do
                var   <- fromEither ztrue $ parse_expr' 
                        (parser `with_vars` symbol_table fv0)
                               { expected_type = Just int }
                        var
                bound <- fromEither ztrue $ parse_expr' -- m WithFreeDummies bound
                        parser { free_dummies = True
                               , expected_type = Just int }
                        bound
                dir  <- case map toLower $ concatMap flatten dir of
                    "up"   -> return Up
                    "down" -> return Down
                    _      -> do
                        tell [Error "expecting a direction for the variant" li]
                        return (error "induction: unreadable")
                return (dir,var,bound)
            Nothing -> left [Error "expecting a variant" li]
            _ -> left [Error "invalid variant" li]
        dum <- case fv1 \\ fv0 of
            [v] -> return v
            _   -> left [Error (   "inductive formula should have one free "
                                ++ "variable to record the variant") li]                    
        add_proof_edge goal_lbl [h0]
        return $ Rule (Induction pr0 h0 pr1 (IntegerVariant dum var bound dir))

instance RefRule ScheduleChange where 
    rule_name     r = 
        case rule r of 
            Replace _ _      -> label "delay"
            Weaken           -> label "weaken"
            ReplaceFineSch _ _ _ _ -> label "replace"
            RemoveGuard _          -> label "grd"
            AddGuard _             -> label "add"
    hyps_labels r = 
        case rule r of
            Replace (lbl,_) _ -> [PId lbl]
            ReplaceFineSch _ _ _ (Just (lbl,_)) -> [PId lbl]
            ReplaceFineSch _ _ _ Nothing -> []
            _ -> []
    supporting_evts _ = []
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
