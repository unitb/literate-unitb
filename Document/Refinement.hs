{-# LANGUAGE FlexibleInstances, FlexibleContexts        #-}
{-# LANGUAGE DeriveDataTypeable, IncoherentInstances    #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables     #-}
{-# LANGUAGE BangPatterns, TemplateHaskell              #-}
module Document.Refinement where

    -- Module
import Document.Phase
import Document.Pipeline
import Document.Proof
import Document.Visitor

import UnitB.AST
import UnitB.PO
import UnitB.POGenerator as POG

import Latex.Parser

import Logic.Expr

import Theories.SetTheory

    -- Libraries
import Control.Arrow (second)
import Control.DeepSeq

import Control.Monad.Trans.Either
import Control.Monad.RWS as RWS

import Data.Char
import Data.DeriveTH
import Data.Either
import Data.List as L ( intercalate, (\\), null )
import qualified Data.List.NonEmpty as NE
import Data.Map as M hiding ( map, (\\) )
import Data.Typeable

import Utilities.Error
import Utilities.Format
import Utilities.Syntactic

add_proof_edge :: MonadState System m 
               => Label -> [Label] -> m ()
add_proof_edge x xs = do
        RWS.modify (\x -> x { proof_struct = edges ++ proof_struct x } )
    where
        edges = zip (repeat x) xs

data RuleParserParameter = 
    RuleParserDecl 
        MachineP2
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
    supporting_evts _ = []

class RuleParser a where
    parse_rule :: a -> [Label] -> String 
               -> RuleParserParameter 
               -> M Rule

instance RefRule a => RuleParser (M a,()) where
    parse_rule (cmd,_) [] _ _ = do 
            x <- cmd
            return $ Rule x
    parse_rule _ hyps_lbls _ _ = do
        li <- lift $ ask
        raise $ Error (format "too many hypotheses in the application of the rule: {0}" 
                          $ intercalate "," $ map show hyps_lbls) li

instance RefRule a => RuleParser (a,()) where
    parse_rule (x,()) xs y z = do
            let cmd = return x :: M a
            parse_rule (cmd,()) xs y z

getProgress :: RuleParserParameter -> Map Label ProgressProp
getProgress (RuleParserDecl _ _ prog _ _ _ _ _ _) = prog

getSafety :: RuleParserParameter -> Map Label SafetyProp
getSafety (RuleParserDecl _ _ _ saf _ _ _ _ _) = saf

getTransient :: RuleParserParameter -> Map Label Transient
getTransient (RuleParserDecl _ _ _ _ tr _ _ _ _) = tr

getGoal :: RuleParserParameter -> Label
getGoal (RuleParserDecl _ _ _ _ _ goal_lbl _ _ _) = goal_lbl

getHypotheses :: RuleParserParameter -> [Label]
getHypotheses (RuleParserDecl _ _ _ _ _ _ hyps_lbls _ _) = hyps_lbls

getHint :: RuleParserParameter -> [LatexDoc]
getHint (RuleParserDecl _ _ _ _ _ _ _ hint _) = hint

getParser :: RuleParserParameter -> ParserSetting
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
                raise $ Error (format "refinement ({0}): {1} should be a progress property" rule x) li
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): expecting more properties" rule) li

instance RuleParser (a,()) => RuleParser (SafetyProp -> a,()) where
    parse_rule (f,_) (x:xs) rule param = do
        let saf = getSafety param
        case M.lookup x saf of
            Just p -> parse_rule (f p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): {1} should be a safety property" rule x) li
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): expecting more properties" rule) li

instance RuleParser (a,()) => RuleParser (Label -> Transient -> a,()) where
    parse_rule (f,_) (x:xs) rule param = do
        let tr = getTransient param
        case M.lookup x tr of
            Just p -> parse_rule (f x p, ()) xs rule param
            Nothing -> do
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): {1} should be a transient predicate" rule x) li
    parse_rule _ [] rule _ = do
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): expecting more properties" rule) li

instance RefRule a => RuleParser ([Label] -> M a, ()) where
    parse_rule (f,_) es rule _ = do
        -- evts <- bind_all x
        li <- lift $ ask
        when (L.null es) 
            $ raise $ Error (format "refinement ({0}): at least one event is required" rule) li
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

instance RefRule a => RuleParser (NE.NonEmpty (Label,ProgressProp) -> a,()) where
    parse_rule (f,_) xs rule param = do
            li <- ask
            when (L.null xs)
                $ raise $ Error (format "refinement ({0}): expecting at least one progress property" rule) li
            parse_rule (g,()) xs rule param
        where
            g = f . NE.fromList

instance RefRule a => RuleParser ([(Label,ProgressProp)] -> a,()) where
    parse_rule (f,_) xs rule param = do
            ps <- forM xs g
            return $ Rule (f $ zip xs ps)        
        where
            prog = getProgress param
            g x = maybe (do
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): {1} should be a progress property" rule x) li )
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
                raise $ Error (format "refinement ({0}): {1} should be a safety property" rule x) li )
                return
                $ M.lookup x saf


parse :: RuleParser a
      => a -> String -> RuleParserParameter
      -> M Rule
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
            let saf = Unless vs p q Nothing
                tr  = Transient (symbol_table vs) 
                                             (p `zand` znot q) lbls 
                                             hint 
            prop_tr m ("", tr)
            tr_wd_po m ("",tr)
            prop_saf m ("", saf)
            saf_wd_po m ("", saf)
    supporting_evts (Ensure _ hyps _) = map EventId hyps

data Discharge = Discharge ProgressProp Label Transient (Maybe SafetyProp)
    deriving (Eq,Typeable,Show)

instance RefRule Discharge where
    rule_name _ = label "discharge"
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

mk_discharge :: ProgressProp -> Label -> Transient -> [SafetyProp] -> Discharge
mk_discharge p lbl tr [s] = Discharge p lbl tr $ Just s
mk_discharge p lbl tr []  = Discharge p lbl tr Nothing
mk_discharge _ _ _ _  = error "expecting at most one safety property" 

parse_discharge :: String -> RuleParserParameter
                -> M Rule
parse_discharge rule params = do
    let goal_lbl = getGoal params
        hyps_lbls = getHypotheses params
    li <- lift $ ask
    when (1 > length hyps_lbls || length hyps_lbls > 2)
        $ raise $ Error (format "too many hypotheses in the application of the rule: {0}"
                            $ intercalate "," $ map show hyps_lbls) li
    add_proof_edge goal_lbl hyps_lbls
    parse (mk_discharge,()) rule params

data Monotonicity = Monotonicity ProgressProp Label ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule Monotonicity where
    rule_name _   = label "monotonicity"
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
    supporting_evts _ = []

data Disjunction = Disjunction ProgressProp [(Label,([Var], ProgressProp))]
    deriving (Eq,Typeable,Show)

instance RefRule Disjunction where
    rule_name _ = label "disjunction"
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

disjunction :: ProgressProp -> [(Label,ProgressProp)] -> Disjunction
disjunction pr0@(LeadsTo fv0 _ _) ps = 
        let f pr1@(LeadsTo fv1 _ _) = (fv1 \\ fv0, pr1)
            ps0 = map (second f) ps
        in (Disjunction pr0 ps0)

data NegateDisjunct = NegateDisjunct ProgressProp Label ProgressProp
    deriving (Eq,Typeable,Show)

instance RefRule NegateDisjunct where
    rule_name _   = label "trading"
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

data Transitivity = Transitivity ProgressProp (NE.NonEmpty (Label,ProgressProp))
    deriving (Eq,Typeable,Show)

instance RefRule Transitivity where
    rule_name _ = label "transitivity"
    supporting_evts _ = []
    refinement_po 
            (Transitivity
                    (LeadsTo fv0 p0 q0)
                    xs )
                    -- (NonEmpty firstLT xs))
                    -- _ (LeadsTo fv1 p1 q1)
                    -- _ (LeadsTo fv2 p2 q2))
            m = do
                let (LeadsTo fv1 p1 _) = snd $ NE.head xs
                    (LeadsTo fv2 _ q2) = snd $ NE.last xs
                    conseq = zip (NE.toList xs) (drop 1 $ NE.toList xs)
                assert m "lhs" ( 
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            p0 `zimplies` p1 )
                forM_ conseq $ \(p,q) -> do
                    let (l1, LeadsTo fv1 _ q1) = p
                        (l2, LeadsTo fv2 p2 _) = q
                    assert m (show $ "mhs" </> l1 </> l2) ( 
                        zforall (fv0 ++ fv1 ++ fv2) ztrue $
                                q1 `zimplies` p2 )
                assert m "rhs" ( 
                    zforall (fv0 ++ fv1 ++ fv2) ztrue $
                            q2 `zimplies` q0 )

data PSP = PSP ProgressProp Label ProgressProp SafetyProp
    deriving (Eq,Typeable,Show)

instance RefRule PSP where
    rule_name _ = label "PSP"
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

data Induction = Induction ProgressProp Label ProgressProp Variant
    deriving (Eq,Typeable,Show)

instance RefRule Induction where
    rule_name _ = label "induction"
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

parse_induction :: String 
                -> RuleParserParameter
                -> M Rule
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
        dum <- case fv1 \\ fv0 of
            [v] -> return v
            _   -> raise $ Error (   "inductive formula should have one free "
                                ++ "variable to record the variant") li 
        var <- case find_cmd_arg 3 ["\\var"] hint of
            Just (_,_,[var,dir,bound],_) -> toEither $ do
                dir  <- case map toLower $ concatMap flatten dir of
                    "up"   -> return Up
                    "down" -> return Down
                    _      -> do
                        tell [Error "expecting a direction for the variant" li]
                        return (error "induction: unreadable")
                var   <- fromEither ztrue $ parse_expr' 
                        (parser `with_vars` symbol_table fv0)
                               { free_dummies = True
                               , expected_type = Nothing }
                        var
                bound <- fromEither ztrue $ parse_expr' -- m WithFreeDummies bound
                        parser { free_dummies = True
                               , expected_type = Just (type_of var) }
                        bound
                let is_set = isRight $ zcast (set_type gA) (Right var)
                if type_of var == int then
                    return (IntegerVariant dum var bound dir)
                else if is_set then
                    return (SetVariant dum var bound dir)
                else do
                    tell [Error 
                        (format "invalid variant type\n\tExpecting: set or integer\n\tActual:  {1}" 
                            (type_of var))
                        li]
                    return ($myError "")
                -- return (dir,var,bound)
            Nothing -> left [Error "expecting a variant" li]
            _ -> left [Error "invalid variant" li]
        add_proof_edge goal_lbl [h0]
        return $ Rule (Induction pr0 h0 pr1 var)


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

derive makeNFData ''Add
derive makeNFData  ''Ensure
derive makeNFData  ''Discharge
derive makeNFData  ''Monotonicity
derive makeNFData  ''Implication
derive makeNFData  ''Disjunction
derive makeNFData  ''NegateDisjunct
derive makeNFData  ''Transitivity
derive makeNFData  ''PSP
derive makeNFData  ''Induction
