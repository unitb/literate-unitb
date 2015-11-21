{-# LANGUAGE IncoherentInstances    #-}
{-# LANGUAGE OverloadedStrings, ScopedTypeVariables     #-}
{-# LANGUAGE BangPatterns, TypeFamilies       #-}
module Document.Refinement where

    -- Module
import Document.Phase
import Document.Phase.Transient
import Document.Proof
import Document.Visitor

import UnitB.AST hiding (assert)

import Latex.Parser

import Logic.Expr hiding (Const)

    -- Libraries
import Control.Arrow (second)
import Control.Lens hiding (Context)

import Control.Monad.RWS as RWS

import Data.Char
import Data.Either
import Data.List as L
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Map as M hiding ( map, (\\) )
import Data.Tuple

import Utilities.Error
import Utilities.Format
import Utilities.Syntactic

data RuleParserParameter = 
    RuleParserDecl 
        { getMachine :: MachineP2
        , getMachineId :: MachineId
        , getProgress :: (Map Label ProgressProp)
        , getSafety :: (Map Label SafetyProp)
        , getTransient :: (Map Label Transient)
        , getGoal :: Label
        , getHypotheses :: [Label]
        , getHint :: LatexDoc
        , getParser :: ParserSetting
        }

type Rule = ProofTree

class ( LivenessRulePO rule
      , Parsable (SafetyHyp rule)
      , Parsable (ProgressHyp rule) )
            => RuleParser rule where

parse_rule :: RuleParser rule
           => rule
           -> LiveParser Rule
parse_rule r = ProofNode r <$> (fmap (second ref.swap) <$> parseProgress r) 
                             <*> (fmap (,Nothing) <$> parseSafety r)
    where
        ref :: ProgId -> ProofTree
        ref pid = ProofNode (Reference pid) (Const ()) (Const ())

type LiveParser = RWST RuleParserParameter () [Label] M

class Parsable f where
    parseMany :: Label
              -> (Label -> M a)
              -> LiveParser (f a)

instance Parsable None where
    parseMany _ _ = return $ Const ()
instance Parsable One where
    parseMany rule f = do
        xs <- get
        case xs of
          x:xs -> do
            put xs
            lift $ Identity <$> f x
          [] -> lift $ do
            li <- ask
            raise $ Error (format "refinement ({0}): expecting more properties" rule) li
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
                raise $ Error (format "refinement ({0}): expecting at most one property" rule) li                

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
                li <- lift $ ask
                raise $ Error (format "refinement ({0}): {1} should be a progress property" rule x) li

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
                    raise $ Error (format "refinement ({0}): {1} should be a safety property" rule x) li

instance RuleParser Induction where
instance RuleParser Disjunction where
instance RuleParser Discharge where
instance RuleParser Monotonicity where
instance RuleParser Implication where
instance RuleParser NegateDisjunct where
instance RuleParser Transitivity where
instance RuleParser PSP where
instance RuleParser Ensure where

parse :: RuleParser rule
      => rule
      -> RuleParserParameter
      -> M Rule
parse rc param = do
        let hyps_lbls = getHypotheses param
        fst <$> evalRWST (parse_rule rc) param hyps_lbls

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
    let hyps_lbls = getHypotheses params
    li <- ask
    when (1 > length hyps_lbls || length hyps_lbls > 2)
        $ raise $ Error (format "too many hypotheses in the application of the rule: {0}"
                            $ intercalate "," $ map show hyps_lbls) li
    parse' params $ do
        transient <- asks getTransient
        let rule = "discharge"
        (lbl,tr) <- parseOne rule $ \lbl -> do
            case M.lookup lbl transient of
                Just p -> return (lbl,getExpr <$> p)
                Nothing -> do
                    li <- ask
                    raise $ Error (format "refinement ({0}): {1} should be a transient predicate" rule lbl) li
        parse_rule (Discharge lbl tr)

parse_induction :: RuleParserParameter
                -> M Rule
parse_induction param = do
        let rule = "induction"
            prog = getProgress param
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
                var   <- fromEither ztrue $
                    getExpr <$> parse_expr'' 
                        (parser `with_vars` symbol_table fv0
                               & free_dummies  .~ True
                               & expected_type .~ Nothing )
                        (flatten_li' var)
                bound <- fromEither ztrue $
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
                        (format "invalid variant type\n\tExpecting: set or integer\n\tActual:  {1}" 
                            (type_of var))
                        li]
                    return ($myError "")
            Nothing -> raise $ Error "expecting a variant" li
            _ -> raise $ Error "invalid variant" li
        parse (Induction var) param

parse_ensure :: RuleParserParameter
             -> M Rule
parse_ensure params = do
        let vs = symbol_table fv
            p2 = getMachine params
            thint = getHint params
            LeadsTo fv _ _ = getProgress params ! getGoal params
            lbls = getHypotheses params
            m    = getMachineId params
        lbls' <- bind  "Expected non empty list of events"
                    $ NE.nonEmpty lbls
        hint <- tr_hint p2 m vs lbls' thint
        lbls <- get_events p2 lbls'
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
