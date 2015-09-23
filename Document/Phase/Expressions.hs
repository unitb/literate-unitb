{-# LANGUAGE TypeOperators, TupleSections #-}
module Document.Phase.Expressions where

    --
    -- Modules
    --
import Document.Expression
import Document.ExprScope as ES
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Structures
import Document.Phase.Transient
import Document.Proof
import Document.Refinement as Ref
import Document.Scope
import Document.VarScope
import Document.Visitor

import Latex.Parser hiding (contents)

import Logic.Expr
import qualified Logic.ExpressionStore as St
import Logic.Operator (Notation)
import Logic.Proof
import Logic.Proof.Tactics hiding ( with_line_info )

import UnitB.AST as AST
import UnitB.PO

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.IntervalTheory
import Theories.PredCalc
import Theories.RelationTheory
import Theories.SetTheory

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import qualified Control.Category as C
import           Control.Applicative 

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.Reader (Reader,runReader,runReaderT)
import           Control.Monad.State.Class 
import           Control.Monad.Writer.Class 
import           Control.Monad.Trans
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Maybe
-- import           Control.Monad.Trans.Reader ( runReaderT )
import           Control.Monad.Trans.RWS as RWS ( RWS, mapRWST )
import qualified Control.Monad.Writer as W

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import           Data.Char
import           Data.Default
import           Data.Either
import           Data.Either.Combinators
import           Data.Functor
import           Data.Graph
import           Data.Map   as M hiding ( map, foldl, (\\) )
import qualified Data.Map   as M
import qualified Data.Maybe as MM
import           Data.Monoid
import           Data.List as L hiding ( union, insert, inits )
import           Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S
import qualified Data.Traversable as T

import qualified Utilities.BipartiteGraph as G
import Utilities.Format
import Utilities.Relation (type(<->),(|>),(<|))
import qualified Utilities.Relation as R
import Utilities.Syntactic

run_phase3_exprs :: Pipeline MM 
            (Hierarchy MachineId, MTable MachineP2) 
            (MTable MachineP3, St.ExprStore)
run_phase3_exprs = second (C.id &&& expressions) >>> liftP (uncurry wrapup)
    where
        err_msg :: Label -> String
        err_msg = format "Multiple expressions with the label {0}"
        wrapup r_ord (p2,es) = do
            let names = M.map (view pEventRenaming) p2
                es' = inherit2 names r_ord . unionsWith (++) <$> es
                store = (St.fromList . concatMap (view exprStore . snd) . concat . M.elems) <$> es'
            exprs <- triggerM
                =<< make_all_tables' err_msg
                =<< triggerM es'
            xs <- T.sequence $ make_phase3 <$> p2 <.> exprs
            store <- triggerM store
            return (xs,store)
        expressions = run_phase 
            [ assignment
            , bcmeq_assgn
            , bcmsuch_assgn
            , bcmin_assgn
            , guard_decl
            , guard_removal
            , coarse_removal
            , fine_removal
            , default_schedule_decl
            , fine_sch_decl
            , coarse_sch_decl
            , initialization
            , assumption
            , invariant
            , mch_theorem
            , transient_prop
            , transientB_prop
            , constraint_prop
            , progress_prop
            , safetyA_prop
            , safetyB_prop
            , remove_assgn
            , remove_init
            , init_witness_decl
            , witness_decl ]

make_phase3 :: MachineP2 -> Map Label ExprScope -> MM MachineP3
make_phase3 p2 exprs' = do
        p3  <- pEventRef (mapEvents 
                    (liftEvent toOldEvtExpr p2) 
                    (liftEvent toNewEvtExpr p2)) 
                =<< pContext newThy p2
        makeMachineP3' p3 
                <$> (makePropertySet <$> liftFieldM toOldPropSet p2 exprs)
                <*> (makePropertySet <$> liftFieldM toNewPropSet p2 exprs)
                <*> liftFieldM toMchExpr p2 exprs
        -- tell errs
        -- unless (L.null errs) $ fail ""
        -- return p3''
    where
        exprs = M.toList exprs'
        liftEvent :: (   Label 
                      -> ExprScope 
                      -> Reader MachineP2 
                                [Either Error (EventId, [EventP3Field])])
                  -> MachineP2
                  -> Maybe EventId -> EventP2 -> MM EventP3
        liftEvent f p2 = \eid e -> makeEventP3 e.(!eid) <$> m
            where m = fromListWith (++).L.map (first Just) <$> liftFieldM f p2 exprs
        newThy t = makeTheoryP3 t <$> liftFieldM toThyExpr t exprs
        -- p3 =  over pContext makeTheoryP3
        --     $ over pEvents (M.map makeEventP3) 
        --       (makeMachineP3' p2)
        -- (p3',errs) = _ $ parseExprScope exprs p3
        -- skip = M.fromList [ (v,Word (prime v) `zeq` Word v) | v <- M.elems $ view newDelVars p3']
        -- p3'' = over pEvents (M.map $ over eWitness (`M.union` skip)) p3'

assignment :: MPipeline MachineP2
                    [(Label,ExprScope)]
assignment = machineCmd "\\evassignment" $ \(ev_lbl, lbl, xs) _m p2 -> do
            ev <- get_event p2 ev_lbl
            (pred,eStore) <- parse_expr''
                (event_parser p2 ev) 
                { is_step = True } 
                xs
            let frame = M.elems $ (p2^.pStateVars) `M.difference` (p2^.pAbstractVars)
                act = BcmSuchThat frame pred
            li <- lift ask
            return [(lbl,evtScope ev (Action (InhAdd act) Local li eStore))]

bcmeq_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmeq_assgn = machineCmd "\\evbcmeq" $ \(ev_lbl, lbl, String v, xs) _m p2 -> do
            let _ = lbl :: Label
            ev <- get_event p2 ev_lbl
            var@(Var _ t) <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (p2^.pStateVars)
            li <- lift ask
            (xp,eStore) <- parse_expr''
                (event_parser p2 ev) 
                { expected_type = Just t } 
                xs
            check_types
                $ Right (Word var :: Expr) `mzeq` Right xp
            let act = Assign var xp
            return [(lbl,evtScope ev (Action (InhAdd act) Local li eStore))]

bcmsuch_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmsuch_assgn = machineCmd "\\evbcmsuch" $ \(evt, lbl, vs, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            (xp,eStore) <- parse_expr'' (event_parser p2 ev)
                    { is_step = True } 
                    xs
            vars <- bind_all (map toString vs)
                (format "variable '{0}' undeclared")
                $ (`M.lookup` (p2^.pStateVars))
            let act = BcmSuchThat vars xp
            return [(lbl,evtScope ev (Action (InhAdd act) Local li eStore))]

bcmin_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmin_assgn = machineCmd "\\evbcmin" $ \(evt, lbl, String v, xs) _m p2 -> do
            ev <- get_event p2 evt
            var@(Var _ t) <- bind
                (format "variable '{0}' undeclared" v)
                $ v `M.lookup` (p2^.pStateVars)
            li  <- lift ask
            (xp,eStore) <- parse_expr'' (event_parser p2 ev)
                    { expected_type = Just (set_type t) } 
                    xs
            let act = BcmIn var xp
            check_types $ Right (Word var) `zelem` Right xp
            return [(lbl,evtScope ev (Action (InhAdd act) Local li eStore))]

instance Scope Initially where
    type Impl Initially = WithDelete Initially

used_var' :: Expr -> Map String Var
used_var' = symbol_table . S.toList . used_var

instance IsExprScope Initially where
    toMchExpr lbl i  = do
        vs <- view pDelVars
        return $ case (i^.inhStatus,i^.declSource) of
            (InhAdd x,_)
                | L.null lis' -> [Right $ PInit lbl x]
                | otherwise   -> [Left $ MLError msg $ (format "predicate {0}" lbl,li):lis']
                where
                    lis = L.map (first name) $ M.elems $ vs `M.intersection` used_var' x
                    lis' = L.map (first (format "deleted variable {0}")) lis
                    msg  = format "initialization predicate '{0}' refers to deleted variables" lbl
            (InhDelete (Just x),Local) -> [Right $ PDelInits lbl x]
            (InhDelete (Just _),Inherited) -> []
            (InhDelete Nothing,_) -> [Left $ Error msg li]
                where
                    msg = format "initialization predicate '{0}' was deleted but does not exist" lbl
        where
            li = i^.lineInfo
    toThyExpr _ _  = return []
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     xs <- forM xs $ \(lbl,x) -> do
    --         case x of
    --             Initially (InhAdd x) _ li _ -> do
    --                 vs <- gets $ view pDelVars
    --                 let msg = format "initialization predicate '{0}' refers to deleted variables" lbl
    --                     lis = L.map (first name) $ M.elems $ vs `M.intersection` used_var' x
    --                     lis' = L.map (first (format "deleted variable {0}")) lis
    --                 unless (L.null lis')
    --                     $ tell [MLError msg $ (format "predicate {0}" lbl,li):lis']
    --                 return ([(lbl,x)],[],[])
    --             Initially (InhDelete (Just x)) Local _ _ -> 
    --                 return ([],[(lbl,x)],[(v,x) | v <- S.elems $ used_var x ])
    --             Initially (InhDelete (Just _)) Inherited _ _ -> 
    --                 return ([],[],[])
    --             Initially (InhDelete Nothing) _ li _ -> do
    --                 let msg = format "initialization predicate '{0}' was deleted but does not exist" lbl
    --                 tell [Error msg li]
    --                 return ([],[],[])
    --     let (ys,zs,ws) = mconcat xs 
    --     pInit     %= M.union (M.fromList ys)
    --     pDelInits %= M.union (M.fromList zs)
    --     pInitWitness %= flip M.union (M.fromList ws)

remove_init :: MPipeline MachineP2 [(Label,ExprScope)]
remove_init = machineCmd "\\removeinit" $ \(One lbls) _m _p2 -> do
            li <- lift ask
            return [(lbl,ExprScope $ Initially (InhDelete Nothing) Local li []) | lbl <- lbls ]

remove_assgn :: MPipeline MachineP2 [(Label,ExprScope)]
remove_assgn = machineCmd "\\removeact" $ \(evt, lbls) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            return [(lbl,evtScope ev (Action (InhDelete Nothing) Local li [])) | lbl <- lbls ]

witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
witness_decl = machineCmd "\\witness" $ \(evt, String var, xp) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            (p,eStore)  <- parse_expr'' (event_parser p2 ev) { is_step = True } xp
            v  <- bind (format "'{0}' is not a disappearing variable" var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            return [(label var,evtScope ev (Witness v p Local li eStore))]

instance Scope EventExpr where
    keep_from s (EventExpr m) = Just $ EventExpr $ M.mapMaybe (keep_from s) m
    make_inherited (EventExpr m) = Just $ EventExpr (M.map f m)
        where
            f x = set declSource Inherited x
    clashes (EventExpr m0) (EventExpr m1) = not $ M.null 
            $ M.filter id
            $ M.intersectionWith clashes m0 m1
    error_item (EventExpr m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' _ = error "Scope ExprScope: head'"
            msg (Just k) sc = (format "{1} (event {0})" k sc :: String, view lineInfo sc)
            msg Nothing sc = (format "{0} (initialization)" sc :: String, view lineInfo sc)
    merge_scopes (EventExpr m0) (EventExpr m1) = EventExpr $ unionWith merge_scopes m0 m1
    rename_events m (EventExpr es) = map EventExpr $ concatMap f $ toList es
        where
            lookup x = MM.fromMaybe [x] $ M.lookup x m
            f (Just eid,x) = [ singleton (Just e) x | e <- lookup eid ]
            f (Nothing,x) = [singleton Nothing x]

checkLocalExpr :: ( HasInhStatus decl (InhStatus expr)
                  , HasLineInfo decl LineInfo )
               => String -> (expr -> Map String Var)
               -> [(Maybe EventId, [(Label,decl)])] 
               -> RWS () [Error] MachineP3 ()
checkLocalExpr expKind free xs = do
        vs <- use pDelVars
        let xs' = [ (eid,lbl,sch) | (e,ss) <- xs, (lbl,sch) <- ss, eid <- MM.maybeToList e ]
        forM_ xs' $ \(eid,lbl,sch) -> do
            case (sch ^. inhStatus) of
                InhAdd expr -> do
                    let msg = format "event '{1}', {2} '{0}' refers to deleted variables" lbl eid expKind
                        errs   = vs `M.intersection` free expr
                        schLI  = (format "{1} '{0}'" lbl expKind, sch ^. lineInfo)
                        varsLI = L.map (first $ format "deleted variable '{0}'" . name) (M.elems errs)
                    unless (M.null errs) 
                        $ tell [MLError msg $ schLI : varsLI]
                InhDelete Nothing -> do
                    let msg = format "event '{1}', {2} '{0}' was deleted but does not exist" lbl eid expKind
                        li  = sch ^. lineInfo
                    tell [Error msg li]
                _ -> return ()

checkLocalExpr' :: ( HasInhStatus decl (InhStatus expr)
                  , HasLineInfo decl LineInfo )
               => String -> (expr -> Map String Var)
               -> EventId -> Label -> decl
               -> Reader MachineP2 [Either Error a]
checkLocalExpr' expKind free eid lbl sch = do
            vs <- view pDelVars 
            return $ case (sch ^. inhStatus) of
                InhAdd expr -> 
                    let msg = format "event '{1}', {2} '{0}' refers to deleted variables" lbl eid expKind
                        errs   = vs `M.intersection` free expr
                        schLI  = (format "{1} '{0}'" lbl expKind, sch ^. lineInfo)
                        varsLI = L.map (first $ format "deleted variable '{0}'" . name) (M.elems errs)
                    in if M.null errs then []
                       else [Left $ MLError msg $ schLI : varsLI]
                InhDelete Nothing -> 
                    let msg = format "event '{1}', {2} '{0}' was deleted but does not exist" lbl eid expKind
                        li  = sch ^. lineInfo
                    in [Left $ Error msg li]
                _ -> []
        -- xs' = [ (eid,lbl,sch) | (e,ss) <- xs, (lbl,sch) <- ss, eid <- MM.maybeToList e ]

parseEvtExpr :: ( HasInhStatus decl (InhStatus Expr)
                , HasLineInfo decl LineInfo
                , HasDeclSource decl DeclSource)
             => String 
             -> (Label -> Expr -> field)
             -> (Label -> Expr -> field)
             -> (Label -> Expr -> field)
             -> EventId -> Label -> decl
             -> Reader MachineP2 [Either Error [field]]
parseEvtExpr x = parseEvtExpr' x used_var'

parseEvtExpr' :: ( HasInhStatus decl (InhStatus expr)
                 , HasLineInfo decl LineInfo
                 -- , HasMchExpr decl expr
                 , HasDeclSource decl DeclSource)
              => String 
              -> (expr -> Map String Var)
              -> (Label -> expr -> field)
              -> (Label -> expr -> field)
              -> (Label -> expr -> field)
              -> EventId -> Label -> decl
              -> Reader MachineP2 [Either Error [field]]
parseEvtExpr' expKind fvars old' del' new' k lbl c = (++) <$> checkLocalExpr' expKind fvars k lbl c 
    <*>
        -- (old_xs, del_xs, new_xs)
        case (c^.inhStatus, c^.declSource) of
            (InhAdd e, Inherited) -> return [ old e, new e ] 
                                       -- ([(k,[x])],[],[(k,[x])])
            (InhAdd e, Local)     -> return [ new e ]
                                       -- ([],[],[(k,[x])])
            (InhDelete _, Inherited) -> return [] -- ([],[],[])
            (InhDelete (Just e), Local) -> return [old e,del e] 
            (InhDelete Nothing, Local) -> return [] 
    where
        old e = Right [old' lbl e]
        new e = Right [new' lbl e]
        del e = Right [del' lbl e]

instance IsEvtExpr CoarseSchedule where
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr = parseEvtExpr "coarse schedule" 
            EOldCoarseSched 
            EDelCoarseSched 
            ENewCoarseSched
--     parseEvtExpr xs = do
--         parseEvtExprChoice' pOldCoarseSched pDelCoarseSched pNewCoarseSched fst xs
--         checkLocalExpr "coarse schedule" used_var' xs

instance IsEvtExpr FineSchedule where
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr = parseEvtExpr "fine schedule"
            EOldFineSched
            EDelFineSched
            ENewFineSched
--     parseEvtExpr xs = do
--         parseEvtExprChoice' pOldFineSched pDelFineSched pNewFineSched fst xs
--         checkLocalExpr "fine schedule" used_var' xs

instance IsEvtExpr Guard where
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr = parseEvtExpr "guard"
            EOldGuards
            EDelGuards
            ENewGuards
--     parseEvtExpr xs = do
--         parseEvtExprChoice' pOldGuards pDelGuards pNewGuards fst xs
--         checkLocalExpr "guard" used_var' xs

guard_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            (xp,eStore) <- parse_expr'' (event_parser p2 ev) xs
            return [(lbl,evtScope ev (Guard (InhAdd xp) Local li eStore))]

guard_removal :: MPipeline MachineP2 [(Label,ExprScope)]
guard_removal = machineCmd "\\removeguard" $ \(evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 evt_lbl
        li <- lift ask
        return [(lbl,evtScope ev (Guard (InhDelete Nothing) Local li [])) | lbl <- lbls ]

coarse_removal :: MPipeline MachineP2 [(Label,ExprScope)]
coarse_removal = machineCmd "\\removecoarse" $ \(evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 evt_lbl
        li <- lift ask
        return [(lbl,evtScope ev (CoarseSchedule (InhDelete Nothing) Local li [])) | lbl <- lbls ]

fine_removal :: MPipeline MachineP2 [(Label,ExprScope)]
fine_removal = machineCmd "\\removefine" $ \(evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 evt_lbl
        li <- lift ask
        return [(lbl,evtScope ev (FineSchedule (InhDelete Nothing) Local li [])) | lbl <- lbls ]

coarse_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
coarse_sch_decl = machineCmd "\\cschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            (xp,eStore) <- parse_expr'' (schedule_parser p2 ev) xs
            return [(lbl,evtScope ev (CoarseSchedule (InhAdd xp) Local li eStore))]

fine_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(evt, lbl, xs) _m p2 -> do
            ev <- get_event p2 evt
            li <- lift ask
            (xp,eStore) <- parse_expr'' (schedule_parser p2 ev) xs
            return [(lbl,evtScope ev (FineSchedule (InhAdd xp) Local li eStore))]

        -------------------------
        --  Theory Properties  --
        -------------------------

instance Scope Axiom where
    merge_scopes _ _ = error "Axiom Scope.merge_scopes: _, _"
    clashes _ _ = True
    keep_from s x = guard (s == f x) >> return x
        where
            f (Axiom _ s _ _) = s
    error_item (Axiom _ _ li _) = ("assumtion", li)

parseExpr' :: (HasMchExpr b a, Ord label)
           => Lens' MachineP3 (Map label a) 
           -> [(label,b)] 
           -> RWS () [Error] MachineP3 ()
parseExpr' ln xs = modify $ ln %~ M.union (M.fromList $ map (second $ view mchExpr) xs)

instance IsExprScope Axiom where
    toMchExpr _ _    = return []
    toThyExpr lbl x  = return [Right $ PAssumptions lbl $ x^.mchExpr]
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr = parseExpr' pAssumptions

assumption :: MPipeline MachineP2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            (xp,eStore) <- parse_expr'' (p2^.pCtxSynt) xs
            return [(lbl,ExprScope $ Axiom xp Local li eStore)]

        --------------------------
        --  Program properties  --
        --------------------------

initialization :: MPipeline MachineP2
                    [(Label,ExprScope)]
initialization = machineCmd "\\initialization" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            (xp,eStore) <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,ExprScope $ Initially (InhAdd xp) Local li eStore)]

default_schedule_decl :: MPipeline MachineP2 [(Label,ExprScope)]
default_schedule_decl = arr $ \p2 -> 
        Just $ M.map (map default_sch . elems . M.map Just . M.mapWithKey const) -- (^. eEventId)) 
             $ M.map (^.pNewEvents) p2
    where
        li = LI "default" 1 1
        default_sch e = ( label "default",
                          ExprScope $ EventExpr 
                            $ singleton e (EvtExprScope $ CoarseSchedule (InhAdd zfalse) Inherited li []))


instance Scope Invariant where
instance IsExprScope Invariant where
    toMchExpr lbl e = return [Right $ PInvariant lbl $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Inv lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Inv lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     parseExpr' pInvariant xs
    --     modifyProps inv xs

invariant :: MPipeline MachineP2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            (xp,eStore) <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,ExprScope $ Invariant xp Local li eStore)]

instance Scope InvTheorem where
instance IsExprScope InvTheorem where
    toMchExpr lbl e = return [Right $ PInvariant lbl $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Inv_thm lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Inv_thm lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     parseExpr' pInvariant xs
    --     modifyProps inv_thm xs

mch_theorem :: MPipeline MachineP2
                    [(Label,ExprScope)]
mch_theorem = machineCmd "\\theorem" $ \(lbl,xs) _m p2 -> do
            li <- lift ask
            (xp,eStore) <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,ExprScope $ InvTheorem xp Local li eStore)]

instance Scope TransientProp where
instance IsExprScope TransientProp where
    toMchExpr lbl e = return [Right $ PTransient lbl $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Transient lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Transient lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     parseExpr' pTransient xs
    --     modifyProps transient xs

transient_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transient_prop = machineCmd "\\transient" $ \(evts, lbl, xs) _m p2 -> do
            _evs <- get_events p2 evts
            li   <- lift ask
            (tr,eStore) <- parse_expr'' (p2^.pMchSynt) 
                    { free_dummies = True } xs
            let withInd = L.filter (not . M.null . (^. eIndices) . ((p2 ^. pEvents) !)) _evs
            toEither $ error_list 
                [ ( not $ L.null withInd
                  , format "event(s) {0} have indices and require witnesses" 
                        $ intercalate "," $ map show withInd) ]
            let vs = symbol_table $ S.elems $ used_var tr
                fv = vs `M.intersection` p2^.pDummyVars
                prop = Tr fv tr evts empty_hint
            return [(lbl,ExprScope $ TransientProp prop Local li eStore)]

transientB_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transientB_prop = machineCmd "\\transientB" $ \(evts, lbl, hint, xs) m p2 -> do
            _evs <- get_events p2 evts
            li   <- lift ask
            (tr,eStore) <- parse_expr'' (p2^.pMchSynt) 
                    { free_dummies = True } xs
            let fv = free_vars' ds tr
                ds = p2^.pDummyVars
            evts' <- bind "Expecting non-empty list of events"
                    $ NE.nonEmpty evts
            hint  <- tr_hint p2 m fv evts' hint
            let prop = Tr fv tr evts hint
            return [(lbl,ExprScope $ TransientProp prop Local li eStore)]

instance IsExprScope ConstraintProp where
    toMchExpr _ _ = return []
    toThyExpr _ _ = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Constraint lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Constraint lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     modifyProps constraint xs

instance Scope ConstraintProp where
    error_item (ConstraintProp _ _ li _) = ("co property", li)

constraint_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
constraint_prop = machineCmd "\\constraint" $ \(lbl,xs) _m p2 -> do
            li  <- lift ask
            (pre,eStore) <- parse_expr'' (p2^.pMchSynt)
                    { free_dummies = True
                    , is_step = True }
                    xs
            let vars = elems $ free_vars' ds pre
                ds = p2^.pDummyVars
                prop = Co vars pre
            return [(lbl,ExprScope $ ConstraintProp prop Local li eStore)]

instance IsExprScope SafetyDecl where
    toMchExpr lbl e = return [Right $ PSafety lbl $ e^.mchExpr]
    toThyExpr _ _    = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Safety lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Safety lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     parseExpr' pSafety xs
    --     modifyProps safety xs

instance Scope SafetyDecl where
    error_item (SafetyProp _ _ li _) = ("safety property", li)

safety_prop :: Label -> Maybe Label
            -> LatexDoc
            -> LatexDoc
            -> MachineId
            -> MachineP2
            -> M [(Label,ExprScope)]
safety_prop lbl evt pCt qCt _m p2 = do
            li <- lift ask
            p <- unfail $ parse_expr'' (p2^.pMchSynt) 
                    { free_dummies = True }
                    pCt
            q <- unfail $ parse_expr'' (p2^.pMchSynt) 
                    { free_dummies = True } 
                    qCt
            maybe (return ()) (void . get_event p2) evt
            (p,eStore)  <- trigger p
            (q,eStore') <- trigger q
            let ds  = p2^.pDummyVars
                dum = free_vars' ds p `union` free_vars' ds q
                new_prop = Unless (M.elems dum) p q evt
            return [(lbl,ExprScope $ SafetyProp new_prop Local li $ eStore ++ eStore')]

safetyA_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
safetyA_prop = machineCmd "\\safety" 
                $ \(lbl, pCt, qCt) -> safety_prop lbl Nothing pCt qCt

safetyB_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
safetyB_prop = machineCmd "\\safetyB" 
                $ \(lbl, evt, pCt, qCt) -> safety_prop lbl evt pCt qCt

instance IsExprScope ProgressDecl where
    toMchExpr lbl e = return [Right $ PProgress (PId lbl) $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Progress lbl $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Progress lbl $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []
    -- parseExpr xs = do
    --     parseExpr' pProgress $ map (first PId) xs
    --     modifyProps progress xs

instance Scope ProgressDecl where
    error_item (ProgressProp _ _ li _) = ("progress property", li)

progress_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
progress_prop = machineCmd "\\progress" $ \(lbl, pCt, qCt) _m p2 -> do
            li <- lift ask
            p    <- unfail $ parse_expr'' (p2^.pMchSynt) 
                    { free_dummies = True }
                    pCt
            q    <- unfail $ parse_expr'' (p2^.pMchSynt) 
                    { free_dummies = True } 
                    qCt
            (p,eStore)  <- trigger p
            (q,eStore') <- trigger q
            let ds  = p2^.pDummyVars
                dum = free_vars' ds p `union` free_vars' ds q
                new_prop = LeadsTo (M.elems dum) p q
--             new_deriv <- bind (format "proof step '{0}' already exists" lbl)
--                 $ insert_new lbl (Rule Add) $ derivation $ props m
            return [(lbl,ExprScope $ ProgressProp new_prop Local li (eStore++eStore'))]

instance IsEvtExpr Witness where
    toMchScopeExpr _ w   
        | w^.declSource == Local = return [Right $ PInitWitness (w^.ES.var) (w^.evtExpr)]
        | otherwise              = return []
    toEvtScopeExpr _ _ w 
        | w^.declSource == Local = return [Right [EWitness (w^.ES.var) (w^.evtExpr)]]
        | otherwise              = return []
    -- parseEvtExpr xs = do
    --     let toExpr = (_witnessVar &&& view evtExpr) . snd
    --         -- isLocal x = x ^. declSource == Local
    --         getLocalExpr = mapA (second $ Kleisli $ is_local) >>> arr (map toExpr)
    --         withEvent    = Kleisli id
    --         withoutEvent = Kleisli $ guard . MM.isNothing
    --         xs' = MM.mapMaybe (runKleisli $ withEvent *** getLocalExpr) xs
    --         ys' = MM.mapMaybe (runKleisli $ withoutEvent *** getLocalExpr >>> arr snd) xs
    --     pWitness %= doubleUnion xs'
    --     pInitWitness %= M.union (M.fromList $ concat ys')

instance IsEvtExpr ActionDecl where
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr eid lbl act = do
            -- vs <- view pDelVars
            -- _
            -- concat <$> sequence 
            --     [ case act of
            --           Action (InhDelete (Just act)) Local _ _ -> _
            --               where f = frame' act `M.intersection` vs
            --                     ns = [ (lbl,Witness v (ba_pred act) Local undefined []) | v <- M.elems f ]
            parseEvtExpr' "action"
                (uncurry M.union . (frame' &&& used_var' . ba_pred))
                EOldActions EDelActions ENewActions 
                eid lbl act
                -- ]
--     parseEvtExpr xs = do
--             parseEvtExprChoice' pOldActions pDelActions pNewActions fst xs
--             vs <- gets $ view pDelVars
--             let xs' = map (uncurry $ \k -> (k,) . concat . MM.mapMaybe (g k)) xs
--                 g (Just _) (lbl,Action (InhDelete (Just act)) Local _ _) = do
--                         let f = frame' act `M.intersection` vs
--                             ns = [ (lbl,Witness v (ba_pred act) Local undefined []) | v <- M.elems f ]
--                         return ns
--                 g _ _ = Nothing
--             parseEvtExprDefault pWitness (_witnessVar . snd) xs'
--             checkLocalExpr "action" 
--                (uncurry M.union . (frame' &&& used_var' . ba_pred)) 
--                 xs

instance IsExprScope EventExpr where
    toMchExpr lbl (EventExpr m) = fmap concat $ mapM (toMchScopeExpr lbl) $ M.elems 
                                        $ M.filterWithKey (const.MM.isNothing) m
    toThyExpr _ _  = return []
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr lbl (EventExpr m) =
            fmap concat $ mapM g $ MM.mapMaybe f $ M.toList m
        where f (x,y) = (,y) <$> x
              g (x,y) = fmap (fmap (x,)) <$> toEvtScopeExpr x lbl y
    toOldEvtExpr lbl (EventExpr m) = 
            fmap concat $ mapM g $ MM.mapMaybe f $ M.toList m
        where f (x,y) = (,y) <$> x
              g (x,y) = fmap (fmap (x,)) <$> toEvtScopeExpr x lbl y
--     parseExpr xs = mapM_ (readEvtExprGroup parseEvtExpr) zs
--         where
--             ys = concatMap g xs
--             zs = groupEvtExprGroup (++) ys
--             g (lbl,EventExpr m) = M.elems $ M.mapWithKey (\eid -> readEvtExprScope $ \e -> EvtExprGroup [(eid,[(lbl,e)])]) m

init_witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
init_witness_decl = machineCmd "\\initwitness" $ \(String var, xp) _m p2 -> do
            -- ev <- get_event p2 evt
            li <- lift ask
            (p,eStore)  <- parse_expr'' (p2^.pMchSynt) xp
            v  <- bind (format "'{0}' is not a disappearing variable" var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            return [(label var, ExprScope $ EventExpr $ M.singleton Nothing (EvtExprScope $ Witness v p Local li eStore))]

event_parser :: HasMachineP2 phase events => phase events thy -> EventId -> ParserSetting
event_parser p2 ev = (p2 ^. pEvtSynt) ! ev

schedule_parser :: HasMachineP2 phase events => phase events thy -> EventId -> ParserSetting
schedule_parser p2 ev = (p2 ^. pSchSynt) ! ev








machine_events :: HasMachineP1 phase events => phase events thy -> Map Label EventId
machine_events p2 = L.view pEventIds p2

evtScope :: IsEvtExpr a => EventId -> a -> ExprScope
evtScope ev x = ExprScope $ EventExpr $ M.singleton (Just ev) (EvtExprScope x)

addEvtExpr :: IsEvtExpr a
           => W.WriterT [(UntypedExpr,[String])] M (EventId,[(UntypedExpr,[String])] -> a) 
           -> M ExprScope
addEvtExpr m = do
    ((ev,f),w) <- W.runWriterT m
    return $ evtScope ev (f w)

check_types :: Either [String] a -> EitherT [Error] (RWS LineInfo [Error] ()) a    
check_types c = EitherT $ do
    li <- ask
    return $ either (\xs -> Left $ map (`Error` li) xs) Right c

free_vars' :: Map String Var -> Expr -> Map String Var
free_vars' ds e = vs `M.intersection` ds
    where
        vs = symbol_table $ S.elems $ used_var e

defaultInitWitness :: MachineP2 -> [MachineP3'Field a b] -> [MachineP3'Field a b]
defaultInitWitness p2 xs = concatMap f xs ++ xs
    where
        vs = p2^.pDelVars
        f (PDelInits _lbl expr) = [PInitWitness v expr
                                    | v <- M.elems $ used_var' expr `M.intersection` vs ]
        f _ = []

defaultEvtWitness :: MachineP2 -> [EventP3Field] -> [EventP3Field]
defaultEvtWitness p2 xs = concatMap f xs ++ xs
    where
        vs = p2^.pDelVars
        f (EDelActions _lbl act) = [EWitness v (ba_pred act) 
                                    | v <- M.elems $ frame' act `M.intersection` vs ]
        f _ = []
