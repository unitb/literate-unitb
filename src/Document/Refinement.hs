{-# LANGUAGE IncoherentInstances    #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE BangPatterns, TypeFamilies       #-}
module Document.Refinement where

    -- Module
import Document.Phase
import Document.Phase.Transient
import Document.Phase.Types
import Document.Proof
import Document.Visitor

import UnitB.Syntax

import Latex.Parser

import Logic.Expr 
import Logic.Expr.Parser

    -- Libraries
import Control.Lens hiding (Context)
import Control.Precondition ((!))

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.RWS as RWS
import Control.Monad.Trans.Either as E

import           Data.Char
import           Data.Default
import           Data.Either
import           Data.Existential
import           Data.List as L
import qualified Data.List.NonEmpty as NE
import           Data.Map as M hiding ( map, (\\), (!) )

import Text.Printf.TH

import Utilities.Error hiding (MonadError)
import Utilities.Syntactic

data RuleParserParameter = 
    RuleParserDecl 
        { getMachine :: MachineP3
        --, getProgress :: Map Label ProgressProp
        --, getSafety :: Map Label SafetyProp
        --, getTransient :: Map Label Transient
        , getGoal :: Label
        , getHypotheses :: [Label]
        , getHint :: LatexDoc
        }

instance Syntactic RuleParserParameter where
    line_info = line_info . getHint
    after = after . getHint
    traverseLineInfo = hintDoc . traverseLineInfo

hintDoc :: Lens' RuleParserParameter LatexDoc
hintDoc f p = (\h' -> p {getHint = h'}) <$> f (getHint p)

getMachineId :: RuleParserParameter -> MachineId
getMachineId = view pMachineId . getMachine

getParser :: RuleParserParameter -> ParserSetting
getParser = view pMchSynt . getMachine

getTransient :: RuleParserParameter -> Map Label Transient
getTransient = view pTransient . getMachine

getProgress :: RuleParserParameter -> Map Label ProgressProp
getProgress = mapKeysMonotonic as_label . view pProgress . getMachine

getNewProgress :: RuleParserParameter -> Map Label ProgressProp
getNewProgress = mapKeysMonotonic as_label . view (pNewPropSet.progress) . getMachine

getSafety :: RuleParserParameter -> Map Label SafetyProp
getSafety = view pSafety . getMachine

getGoalProp :: RuleParserParameter -> M ProgressProp
getGoalProp p = do
    bind ([s|goal %s is not a valid progress property|] (pretty $ getGoal p)) 
        (M.lookup (getGoal p) (getNewProgress p))

type Rule = ProofTree
newtype RuleProxy = RuleProxy { _ruleProxyCell :: Cell1 Proxy RuleParser }

class ( LivenessRulePO rule
      , Parsable (SafetyHyp rule)
      , Parsable (TransientHyp rule)
      , Parsable (ProgressHyp rule) )
            => RuleParser rule where
    makeEventList :: Proxy rule
                  -> [label] 
                  -> M (EventSupport rule label)
    default makeEventList :: EventSupport rule ~ None
                          => Proxy rule 
                          -> [label] 
                          -> M (EventSupport rule label)
    makeEventList _ [] = return Proxy
    makeEventList _ (_:_) = raise' $ Error "expecting no events" 
    promoteRule :: MachineP3
                -> Inference (Proxy rule) 
                -> EventSupport rule Label
                -> LatexDoc
                -> M rule
    default promoteRule :: (Default rule, EventSupport rule ~ None)
                        => MachineP3
                        -> Inference (Proxy rule) 
                        -> EventSupport rule Label
                        -> LatexDoc
                        -> M rule
    promoteRule _ _ _ _ = return def

class Parsable f where
    parseMany :: Label
              -> (Label -> M a)
              -> LiveParser (f a)

type LiveParser = RWST RuleParserParameter () [Label] M

makeFields ''RuleProxy

parse_rule :: RuleParser rule
           => RawProgressProp
           -> rule
           -> LiveParser Rule
parse_rule g r = proofNode g r <$> (fmap ref <$> parseProgress r) 
                               <*> (parseTransient r)
                               <*> (fmap (,Nothing) <$> parseSafety r)
    where
        ref :: (ProgId,RawProgressProp) -> ProofTree
        ref (pid,prop) = proofNode prop (Reference pid) Proxy Proxy Proxy


instance Parsable None where
    parseMany _ _ = return Proxy
instance Parsable One where
    parseMany rule f = do
        xs <- get
        case xs of
          x:xs -> do
            put xs
            lift $ Identity <$> f x
          [] -> lift $ do
            li <- ask
            raise $ Error ([s|refinement (%s): expecting more properties|] (pretty rule)) li
instance Parsable [] where
    parseMany _ f = do
        xs <- get
        put []
        lift $ mapM f xs

instance Parsable Maybe where
    parseMany rule f = do
        xs <- get
        put []
        lift $ case xs of
            [] -> return Nothing
            [x] -> Just <$> f x
            _   -> do
                li <- ask
                raise $ Error ([s|refinement (%s): expecting at most one property|] (pretty rule)) li                

instance Parsable NonEmpty where
    parseMany r f = (:|) <$> parseOne r f
                         <*> parseMany r f

parseProgress :: (LivenessRule rule, Parsable f) 
              => rule
              -> LiveParser (f (ProgId, RawProgressProp))
parseProgress r = do
    prog <- asks getProgress
    let rule = rule_name r
    parseMany rule $ \x -> do
        case M.lookup x prog of
            Just p -> return (PId x, getExpr <$> p)
            Nothing -> do
                li <- ask
                raise $ Error ([s|refinement (%s): %s should be a progress property|] 
                            (pretty rule) (pretty x)) li

parseTransient :: (LivenessRule rule, Parsable f) 
               => rule
               -> LiveParser (f RawTransient)
parseTransient r = do
        saf <- asks getTransient
        let rule = rule_name r
        parseMany rule $ \lbl -> 
            case M.lookup lbl saf of
                Just p -> return $ getExpr <$> p
                Nothing -> do
                    li <- ask
                    raise $ Error ([s|refinement (%s): %s should be a safety property|] 
                            (pretty rule) (pretty lbl)) li

parseSafety :: (LivenessRule rule, Parsable f) 
            => rule
            -> LiveParser (f RawSafetyProp)
parseSafety r = do
        saf <- asks getSafety
        let rule = rule_name r
        parseMany rule $ \x -> 
            case M.lookup x saf of
                Just p -> return $ getExpr <$> p
                Nothing -> do
                    li <- ask
                    raise $ Error ([s|refinement (%s): %s should be a safety property|] 
                                (pretty rule) (pretty x)) li

instance RuleParser Induction where
    promoteRule m (Inference g Proxy (Identity st) Proxy Proxy) _ hint = do
        let (LeadsTo fv0 _ _) = g
            (LeadsTo fv1 _ _) = st^.goal
            parser = m^.pMchSynt
            syntax = "Syntax: \\var{expr}{dir}{bound}"
        li <- ask
        dum <- case fv1 \\ fv0 of
            [v] -> return v
            _   -> raise $ Error (   "inductive formula should have one free "
                                ++ "variable to record the variant") li 
        var <- case find_cmd_arg 3 ["\\var"] hint of
            Just (_,_,[var,dir,bound],_) -> toEither $ do
                dir  <- case map toLower $ flatten' dir of
                    "up"   -> return Up
                    "down" -> return Down
                    _      -> do
                        tell [Error "expecting a direction for the variant" li]
                        return (error "induction: unreadable")
                var   <- fromEither ztrue $ _unM $
                    getExpr <$> parse_expr'' 
                        (parser `with_vars` symbol_table fv0
                               & free_dummies  .~ True
                               & expected_type .~ Nothing )
                        (flatten_li' var)
                bound <- fromEither ztrue $ _unM $
                    getExpr <$> parse_expr''
                        (parser & free_dummies  .~ True
                                & expected_type .~ Just (type_of var) )
                        (flatten_li' bound)
                let is_set = isRight $ zcast (set_type gA) (Right var)
                if type_of var == int then
                    return (IntegerVariant dum var bound dir)
                else if is_set then
                    return (SetVariant dum var bound dir)
                else do
                    tell [Error 
                        ([s|invalid variant type\n\tExpecting: set or integer\n\tActual:  %s\n\t%s|] 
                            (pretty $ type_of var) syntax)
                        li]
                    return ($myError "")
            Nothing -> raise $ Error ("expecting a variant. " ++ syntax) li
            _ -> raise $ Error ("invalid variant. " ++ syntax) li
        return (Induction var)

instance RuleParser Disjunction where
instance RuleParser Discharge where
    promoteRule _ _ _ _ = return Discharge
instance RuleParser Monotonicity where
instance RuleParser Implication where
instance RuleParser NegateDisjunct where
instance RuleParser Transitivity where
instance RuleParser PSP where
instance RuleParser Reference where
    makeEventList Proxy xs = do
        case xs of
            [x] -> return $ Identity x
            _   -> raise' $ Error "expecting exactly one label"
    promoteRule m _ (Identity ref) _ = do
        let pid = PId ref
        unless (pid `M.member` (m^.pProgress))
            $ raise' $ Error $ [s|invalid progress property: %s|] $ pretty ref
        return $ Reference pid
instance RuleParser Ensure where
    makeEventList Proxy xs = do
        bind "expecting at least one event" (NE.nonEmpty xs)
    promoteRule m proof evts hint = do
        let LeadsTo dum _ _ = proof^.goal
        evts' <- bind_all evts 
            ([s|invalid event name: %s|] . pretty) 
            (`M.lookup` (m^.pEventIds))
        hint <- tr_hint m 
                (symbol_table dum)
                evts hint
        return $ Ensure evts' (asExpr <$> hint)

parse :: RuleParser rule
      => rule
      -> RuleParserParameter
      -> M Rule
parse rc param = do
        goal <- fmap getExpr <$> getGoalProp param
        let hyps_lbls = getHypotheses param
        fst <$> evalRWST (parse_rule goal rc) param hyps_lbls

parse' :: RuleParserParameter
       -> LiveParser Rule
       -> M Rule
parse' param cmd = do
        let hyps_lbls = getHypotheses param
        fst <$> evalRWST cmd param hyps_lbls

parseOne :: Label -> (Label -> M b) -> LiveParser b
parseOne rule f = runIdentity <$> parseMany rule f

parse_discharge :: RuleParserParameter
                -> M Rule
parse_discharge params = do
    goal <- fmap getExpr <$> getGoalProp params
    --let hyps_lbls = getHypotheses params
    --li <- ask
    --when (1 > length hyps_lbls || length hyps_lbls > 2)
    --    $ raise $ Error ([s|too many hypotheses in the application of the rule: {0}|]
    --                        $ intercalate "," $ map show hyps_lbls) li
    parse' params $ do
        --transient <- asks getTransient
        --let rule = "discharge"
        --(lbl,tr) <- parseOne rule $ \lbl -> do
        --    case M.lookup lbl transient of
        --        Just p -> return (lbl,getExpr <$> p)
        --        Nothing -> do
        --            li <- ask
        --            raise $ Error ([s|refinement ({0}): {1} should be a transient predicate|] rule lbl) li
        parse_rule goal Discharge -- (Discharge lbl tr)

parse_induction :: RuleParserParameter
                -> M Rule
parse_induction param = do
        let rule = "induction" 
            prog = getProgress param
            goal_lbl  = getGoal param
            hyps_lbls = getHypotheses param
            hint = getHint param
            parser = getParser param
        li <- ask
        toEither $ error_list
            [   ( length hyps_lbls /= 1
                , [s|too many hypotheses in the application of the rule: %s|] 
                    $ intercalate "," $ map pretty hyps_lbls)
            ]
        let h0 = head hyps_lbls
        toEither $ error_list
            [   ( not (goal_lbl `member` prog)
                , [s|refinement (%s): %s should be a progress property|] rule (pretty goal_lbl) )
            ,   ( not (h0 `member` prog)
                , [s|refinement (%s): %s should be a progress property|] rule (pretty h0) )
            ]
        let (LeadsTo fv0 _ _) = getExpr <$> (prog ! goal_lbl)
            (LeadsTo fv1 _ _) = getExpr <$> (prog ! h0)
        dum <- case fv1 \\ fv0 of
            [v] -> return v
            _   -> raise $ Error (   "inductive formula should have one free "
                                ++ "variable to record the variant") li 
        var <- case find_cmd_arg 3 ["\\var"] hint of
            Just (_,_,[var,dir,bound],_) -> toEither $ do
                dir  <- case map toLower $ flatten' dir of
                    "up"   -> return Up
                    "down" -> return Down
                    _      -> do
                        tell [Error "expecting a direction for the variant" li]
                        return (error "induction: unreadable")
                li    <- ask
                var   <- fromEither ztrue $ _unM $
                    getExpr <$> parse_expr'' 
                        (parser `with_vars` symbol_table fv0
                               & free_dummies  .~ True
                               & expected_type .~ Nothing )
                        (flatten_li' var)
                bound <- fromEither ztrue $ _unM $
                    getExpr <$> parse_expr''
                        (parser & free_dummies  .~ True
                                & expected_type .~ Just (type_of var) )
                        (flatten_li' bound)
                let is_set = isRight $ zcast (set_type gA) (Right var)
                if type_of var == int then
                    return (IntegerVariant dum var bound dir)
                else if is_set then
                    return (SetVariant dum var bound dir)
                else do
                    tell [Error 
                        ([s|invalid variant type\n\tExpecting: set or integer\n\tActual:  %s|] 
                            (pretty $ type_of var))
                        li]
                    return ($myError "")
            Nothing -> raise $ Error "expecting a variant" li
            _ -> raise $ Error "invalid variant" li
        parse (Induction var) param

type RuleParser' rule = ProgressProp 
                     -> Inference (Proxy rule) 
                     -> EitherT [Error] (Reader RuleParserParameter) (Inference rule)

parse_ensure' :: RuleParser' Ensure
parse_ensure' goal inf = do
        params <- ask
        let vs = symbol_table fv
            p3 = getMachine params
            thint = getHint params
            LeadsTo fv _ _ = goal
            evts = getHypotheses params
        evts' <- get_events p3
            =<< bind  "Expected non empty list of events"
                    (NE.nonEmpty evts)
        hint  <- E.hoistEither $ tr_hintV p3 vs evts' thint
        return $ inf & ruleLens .~ Ensure evts' (getExpr <$> hint)

parse_ensure :: RuleParserParameter
             -> M Rule
parse_ensure params = do
        let vs = symbol_table fv
            p2 = getMachine params
            thint = getHint params
            LeadsTo fv _ _ = getProgress params ! getGoal params
            lbls = getHypotheses params
        lbls' <- bind  "Expected non empty list of events"
                    $ NE.nonEmpty lbls
        hint  <- tr_hint p2 vs lbls' thint
        lbls  <- get_events p2 lbls'
        parse (Ensure lbls (getExpr <$> hint)) params

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
