{-# LANGUAGE TypeOperators
    , Arrows
    , TypeFamilies
    , OverloadedStrings
    , ViewPatterns
    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Document.Phase.Expressions where

    --
    -- Modules
    --
import Document.ExprScope as ES
import Document.Pipeline
import Document.Phase as P
import Document.Phase.Parameters
import Document.Phase.Transient
import Document.Phase.Types
import Document.Proof
import Document.Scope
import Document.Visitor

import Logic.Expr.Parser

import UnitB.Expr
import UnitB.Syntax as AST hiding (invariant)

    --
    -- Libraries
    --
import Control.Arrow hiding (left,app) -- (Arrow,arr,(>>>))
import qualified Control.Category as C
import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)
import Control.Lens.Misc

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.Reader (Reader)
import           Control.Monad.State.Class 
import           Control.Monad.Trans.RWS as RWS ( RWS )
import qualified Control.Monad.Writer as W

import Control.Precondition

import           Data.Either 
import           Data.Existential
import           Data.Functor.Compose
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.List.NonEmpty as NE
import           Data.Map   as M hiding ( map, (\\), (!) )
import qualified Data.Map   as M
import           Data.Semigroup
import qualified Data.Traversable   as T

import Test.QuickCheck hiding (label)
import Test.QuickCheck.Report
import Test.QuickCheck.ZoomEq

import Text.Printf.TH
import Text.Show.With

import Utilities.Syntactic

withHierarchy :: Pipeline MM (Hierarchy MachineId,MMap a) (MMap b)
              -> Pipeline MM (SystemP a) (SystemP b)
withHierarchy cmd = proc (SystemP ref tab) -> do
    tab' <- cmd -< (ref,tab)
    returnA -< SystemP ref tab'

run_phase3_exprs :: Pipeline MM SystemP2 SystemP3
run_phase3_exprs = -- withHierarchy $ _ *** expressions >>> _ -- (C.id &&& expressions) >>> _ -- liftP (uncurry wrapup)
        proc (SystemP ref tab) -> do
            es <- expressions -< tab
            x  <- liftP id -< wrapup ref tab es
            returnA -< SystemP ref x
    where
        err_msg :: Label -> String
        err_msg = [s|Multiple expressions with the label %s|] . pretty
        wrapup :: Hierarchy MachineId
               -> MMap MachineP2 
               -> Maybe [Map MachineId [(Label, ExprScope)]]
               -> MM' Input (MMap MachineP3)
        wrapup r_ord p2 es = do
            let es' :: Maybe (MMap [(Label, ExprScope)])
                es' = inherit2 p2 r_ord . unionsWith (++) <$> es
            exprs <- triggerM
                =<< make_all_tables' err_msg
                =<< triggerM es'
            let _ = exprs :: MMap (Map Label ExprScope)
            T.sequence $ make_phase3 <$> p2 <.> exprs
        expressions = run_phase 
            [ assignment
            , bcmeq_assgn
            , bcmsuch_assgn
            , bcmin_assgn
            , guard_decl
            , guard_removal
            , coarse_removal
            , fine_removal
            , fine_sch_decl
            , C.id &&& coarse_sch_decl 
                >>> arr snd &&& default_schedule_decl 
                >>> arr (\(x,y) -> M.unionWith (++) <$> x <*> y)
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

make_phase3 :: MachineP2 -> Map Label ExprScope -> MM' c MachineP3
make_phase3 p2 exprs' = triggerLenient $ do
        m <- join $ upgradeM
            newThy newMch
            <$> liftEvent toOldEvtExpr
            <*> liftEvent2 toNewEvtExpr toNewEvtExprDefault
            <*> pure p2
        return m -- & pNewEvents %~ removeDefault

    where
        exprs :: [(Label, ExprScope)]
        exprs = M.toList exprs'
        liftEvent2 :: (   Label 
                      -> ExprScope 
                      -> Reader MachineP2
                                [Either Error (EventId, [EventP3Field])])
                   -> (   Label 
                      -> ExprScope 
                      -> Reader MachineP2
                                [Either Error (EventId, [EventP3Field])])
                   -> MM' c (MachineP2
                        -> SkipOrEvent -> EventP2 -> MM' c EventP3)
        liftEvent2 f g = do
            m <- fromListWith (++).L.map (first Right) <$> liftFieldMLenient f p2 exprs
            m' <- fromListWith (++).L.map (first Right) <$> liftFieldMLenient g p2 exprs
            let _ = m :: Map SkipOrEvent [EventP3Field]
            let ms = M.unionsWith (++) [m', m, M.singleton (Left SkipEvent) [ECoarseSched "default" zfalse]]
            return $ \_ eid e -> return $ makeEventP3 e (findWithDefault [] eid ms)
        liftEvent :: (   Label 
                      -> ExprScope 
                      -> Reader MachineP2
                                [Either Error (EventId, [EventP3Field])])
                  -> MM' c (
                        MachineP2
                        -> SkipOrEvent -> EventP2 -> MM' c EventP3)
        liftEvent f = liftEvent2 f (\_ _ -> return [])
        newMch :: MachineP2
               -> MM' c (MachineP3' EventP2 EventP2 TheoryP2)
        newMch m = makeMachineP3' m 
                <$> (makePropertySet' <$> liftFieldMLenient toOldPropSet m exprs)
                <*> (makePropertySet' <$> liftFieldMLenient toNewPropSet m exprs)
                <*> liftFieldMLenient toMchExpr m exprs
        newThy t = makeTheoryP3 t <$> liftFieldMLenient toThyExpr t exprs

assignment :: MPipeline MachineP2
                    [(Label,ExprScope)]
assignment = machineCmd "\\evassignment" $ \(Conc evt, NewLabel lbl, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            pred <- parse_expr''
                (event_parser p2 ev & is_step .~ True) 
                xs
            let frame = M.elems $ (p2^.pStateVars) `M.difference` (p2^.pAbstractVars)
                act = BcmSuchThat frame pred
            li <- ask
            return [(lbl,evtScope ev (Action (InhAdd (pure (ev,li),act)) Local $ pure li))]

bcmeq_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmeq_assgn = machineCmd "\\evbcmeq" $ \(Conc evt, NewLabel lbl, VarName v, Expr xs) _m p2 -> do
            let _ = lbl :: Label
            ev <- get_event p2 $ as_label (evt :: EventId)
            var@(Var _ t) <- bind
                ([s|variable '%s' undeclared|] $ render v)
                $ v `M.lookup` (p2^.pStateVars)
            li <- ask
            xp <- parse_expr''
                (event_parser p2 ev & expected_type .~ Just t)
                xs
            _ <- check_types
                $ Right (Word var :: RawExpr) `mzeq` Right (asExpr xp)
            let act = Assign var xp
            return [(lbl,evtScope ev (Action (InhAdd (pure (ev,li),act)) Local $ pure li))]

bcmsuch_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmsuch_assgn = machineCmd "\\evbcmsuch" $ \(Conc evt, NewLabel lbl, vs, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr''
                    (event_parser p2 ev & is_step .~ True)
                    xs
            vars <- bind_all (map getVarName vs)
                ([s|variable '%s' undeclared|] . render)
                $ (`M.lookup` (p2^.pStateVars))
            let act = BcmSuchThat vars xp
            return [(lbl,evtScope ev (Action (InhAdd (pure (ev,li),act)) Local $ pure li))]

bcmin_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmin_assgn = machineCmd "\\evbcmin" $ \(Conc evt, NewLabel lbl, VarName v, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            var@(Var _ t) <- bind
                ([s|variable '%s' undeclared|] $ render v)
                $ v `M.lookup` (p2^.pStateVars)
            li  <- ask
            xp <- parse_expr''
                    (event_parser p2 ev & expected_type .~ Just (set_type t) )
                    xs
            let act = BcmIn var xp
            _ <- check_types $ Right (Word var) `zelem` Right (asExpr xp)
            return [(lbl,evtScope ev (Action (InhAdd (pure (ev,li),act)) Local $ pure li))]

instance IsExprScope Initially where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl i  = do
        vs  <- view pDelVars
        mid <- view pMachineId
        return $ case (i^.inhStatus,i^.declSource) of
            (InhAdd x,_)
                | L.null lis' -> [Right $ PInit lbl x]
                | otherwise   -> [Left $ MLError msg $ ([s|predicate %s|] $ pretty lbl,li) :| lis']
                where
                    lis = L.map (first $ view name) $ M.elems $ vs `M.intersection` used_var' x
                    lis' = L.map (first ([s|deleted variable %s|] . render)) lis
                    msg  = [s|In '%s', initialization predicate '%s' refers to deleted symbols|] 
                                    (pretty mid) (pretty lbl)
            (InhDelete (Just x),Local) -> [Right $ PDelInits lbl x]
            (InhDelete (Just _),Inherited) -> []
            (InhDelete Nothing,_) -> [Left $ Error msg li]
                where
                    msg = [s|initialization predicate '%s' was deleted but does not exist|] $ pretty lbl
        where
            li = i^.lineInfo
    toThyExpr _ _  = return []
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

remove_init :: MPipeline MachineP2 [(Label,ExprScope)]
remove_init = machineCmd "\\removeinit" $ \(Identity lbls) _m _p2 -> do
            li <- ask
            return [(lbl,makeCell $ Initially (InhDelete Nothing) Local li) | Abs (InitLbl lbl) <- lbls ]

remove_assgn :: MPipeline MachineP2 [(Label,ExprScope)]
remove_assgn = machineCmd "\\removeact" $ \(Conc evt, lbls) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            return [(lbl,evtScope ev (Action (InhDelete Nothing) Local $ pure li)) | Abs (ActionLbl lbl) <- lbls ]

witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
witness_decl = machineCmd "\\witness" $ \(Conc evt, VarName var, Expr xp) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            let disappear  = (DeletedVar,  ) <$> (p2^.pAbstractVars) `M.difference` (p2^.pStateVars)
                newIndices = (AddedIndex,  ) <$> p2^.evtMergeAdded ev eIndices
                delParams  = (DeletedParam,) <$> p2^.evtMergeDel ev eIndices
            (isVar,v)  <- bind 
                ([s|'%s' is not a disappearing variable or a new index|] (render var))
                (var `M.lookup` (disappear `M.union` newIndices `M.union` delParams))
            p  <- parse_expr'' (event_parser p2 ev &~ do 
                        is_step .= True
                        decls %= insert_symbol v ) xp
            return $ case isVar of
                DeletedVar   -> [(label $ render var,evtScope ev (Witness v p Local $ pure li))]
                AddedIndex   -> [(label $ render var,evtScope ev (IndexWitness v p Local $ pure li))]
                DeletedParam -> [(label $ render var,evtScope ev (ParamWitness v p Local $ pure li))]

instance ZoomEq EventExpr where
instance Scope EventExpr where
    kind (EventExpr m) = show $ ShowString . kind <$> m
    keep_from s (EventExpr m) = Just $ EventExpr $ M.mapMaybe (keep_from s) m
    make_inherited (EventExpr m) = Just $ EventExpr (M.map f m)
        where
            f x = set declSource Inherited x
    error_item (EventExpr m) = setToNeList
            $ sconcat $ NE.fromList $ map sequenceA $ elems $ mapWithKey msg m
        where
            msg (Right k) sc 
                | inheritedFrom sc `elem` [[],[k]]
                    = ([s|%s (event '%s')|] (kind sc) (pretty k) :: String, view lineInfo sc)
                | otherwise
                    = ([s|%s (event '%s', from '%s')|] (kind sc) (pretty k) parents :: String, view lineInfo sc)
                where
                    parents = intercalate "," $ map pretty $ inheritedFrom sc
            msg (Left _) sc = ([s|%s (initialization)|] (kind sc) :: String, view lineInfo sc)
    merge_scopes' (EventExpr m0) (EventExpr m1) = EventExpr <$> scopeUnion merge_scopes' m0 m1
    rename_events' lookup (EventExpr es) = map EventExpr $ concatMap f $ toList es
        where
            f (Right eid,x) = [ singleton (Right e) $ setSource eid (x^.lineInfo) x | e <- lookup eid ]
            f (Left InitEvent,x) = [singleton (Left InitEvent) x]            

checkLocalExpr' :: ( HasInhStatus decl (InhStatus expr)
                  , PrettyPrintable decl
                  , HasLineInfo decl (NonEmptyListSet LineInfo) )
                => String -> (expr -> Map Name Var)
                -> EventId -> Label -> decl
                -> Reader MachineP2 [Either Error a]
checkLocalExpr' expKind free eid lbl sch = do
            vs  <- view pDelVars
            is  <- view $ getEvent eid.eDelIndices
            mid <- view $ pMachineId.to pretty
            return $ case sch^.inhStatus of
                InhAdd expr -> 
                    let msg = [s|In '%s', event '%s', %s '%s' refers to deleted symbols|] 
                                    mid (pretty eid) expKind (pretty lbl)
                        fv = symbKind "variable"
                        fi = symbKind "index"
                        symbKind :: (HasName s1 Name)
                                 => String 
                                 -> Map k1 (s1, d1) 
                                 -> Map k1 (String, d1)
                        symbKind sym = M.map $ first $ [s|deleted %s '%s'|] sym . render . view name
                        fvars  = free expr
                        errs   = fv (vs `M.intersection` fvars) `M.union` fi (is `M.intersection` fvars)
                        schLI  = ([s|%s '%s'|] expKind $ pretty lbl,) <$> sch^.lineInfo
                        varsLI = M.elems errs
                        app (x :| xs) ys = x :| (xs ++ ys)
                    in if M.null errs 
                       then []
                       else [Left $ MLError msg $ setToNeList schLI `app` varsLI]
                InhDelete Nothing -> 
                    let msg = [s|event '%s', %s '%s' was deleted but does not exist|] (pretty eid) expKind (pretty lbl)
                        li  = isOne . setToNeList $ ([s|%s '%s'|] expKind $ pretty lbl,) <$> sch^.lineInfo
                    in [Left $ either (MLError msg) (Error msg.snd) li]
                _ -> []
    where
        isOne (x:|[]) = Right x
        isOne (x:|xs) = Left (x:|xs)

parseEvtExpr :: ( HasInhStatus decl (EventInhStatus Expr)
                , HasLineInfo decl (NonEmptyListSet LineInfo)
                , PrettyPrintable decl
                , HasDeclSource decl DeclSource)
             => String 
             -> (Label -> Expr -> field)
             -> RefScope
             -> EventId -> Label -> decl
             -> Reader MachineP2 [Either Error (EventId,[field])]
parseEvtExpr expKind = parseEvtExpr' expKind used_var'

parseEvtExpr' :: ( HasInhStatus decl (EventInhStatus expr)
                 , HasLineInfo decl (NonEmptyListSet LineInfo)
                 , PrettyPrintable decl
                 , HasDeclSource decl DeclSource)
              => String 
              -> (expr -> Map Name Var)
              -> (Label -> expr -> field)
              -> RefScope
              -> EventId -> Label -> decl
              -> Reader MachineP2 [Either Error (EventId,[field])]
parseEvtExpr' expKind fvars field = parseEvtExpr'' expKind fvars (const . field)

parseEvtExpr'' :: ( HasInhStatus decl (EventInhStatus expr)
                  , HasLineInfo decl (NonEmptyListSet LineInfo)
                  , PrettyPrintable decl
                  , HasDeclSource decl DeclSource)
               => String 
               -> (expr -> Map Name Var)
               -> (Label -> NonEmptyListSet LineInfo -> expr -> field)
               -> RefScope
               -> EventId -> Label -> decl
               -> Reader MachineP2 [Either Error (EventId,[field])]
parseEvtExpr'' expKind fvars field scope evt lbl decl = do
    (++) <$> check
         <*>
        -- (old_xs, del_xs, new_xs)
        case (decl^.inhStatus, decl^.declSource) of
            (InhAdd e, Inherited) -> return $ old e ++ new e 
            (InhAdd e, Local)     -> return $ new e
            (InhDelete _, Inherited) -> return [] 
            (InhDelete (Just e), Local) -> return $ old e
            (InhDelete Nothing, Local)  -> return [] 
    where
        check = case scope of
                    Old -> return []
                    New -> checkLocalExpr' expKind (fvars.snd) evt lbl decl
        old = case scope of
            Old -> \(evts,e) -> [Right (ev,[field lbl (pure li) e]) | (ev,li) <- setToList evts]
            New -> const []
        new = case scope of
            Old -> const []
            New -> \(_,e) -> [Right (evt,[field lbl (decl^.lineInfo) e])]

instance IsEvtExpr CoarseSchedule where
    toMchScopeExpr _ _    = return []
    defaultEvtWitness _ _ = return []
    toEvtScopeExpr = parseEvtExpr "coarse schedule" ECoarseSched

instance IsEvtExpr FineSchedule where
    toMchScopeExpr _ _    = return []
    defaultEvtWitness _ _ = return []
    toEvtScopeExpr = parseEvtExpr "fine schedule" EFineSched

instance IsEvtExpr Guard where
    toMchScopeExpr _ _  = return []
    defaultEvtWitness _ _ = return []
    toEvtScopeExpr = parseEvtExpr "guard" EGuards

guard_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(Conc evt, NewLabel lbl, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr'' (event_parser p2 ev) xs
            return [(lbl,evtScope ev (Guard (InhAdd (pure (ev,li),xp)) Local $ pure li))]

guard_removal :: MPipeline MachineP2 [(Label,ExprScope)]
guard_removal = machineCmd "\\removeguard" $ \(Conc evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 $ as_label (evt_lbl :: EventId)
        li <- ask
        return [(lbl,evtScope ev (Guard (InhDelete Nothing) Local $ pure li)) | Abs (GuardLbl lbl) <- lbls ]

coarse_removal :: MPipeline MachineP2 [(Label,ExprScope)]
coarse_removal = machineCmd "\\removecoarse" $ \(Conc evt_lbl, lbls) _m p2 -> do
        ev  <- get_event p2 $ as_label (evt_lbl :: EventId)
        li <- ask
        return [(lbl,evtScope ev (CoarseSchedule (InhDelete Nothing) Local $ pure li)) | Abs (CoarseSchLbl lbl) <- lbls ]

fine_removal :: MPipeline MachineP2 [(Label,ExprScope)]
fine_removal = machineCmd "\\removefine" $ \(Conc evt_lbl,lbls) _m p2 -> do
        ev  <- get_event p2 $ as_label (evt_lbl :: EventId)
        li <- ask
        return [(lbl,evtScope ev (FineSchedule (InhDelete Nothing) Local $ pure li)) | Abs (FineSchLbl lbl) <- lbls ]

coarse_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
coarse_sch_decl = machineCmd "\\cschedule" $ \(Conc evt, NewLabel lbl, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr'' (schedule_parser p2 ev) xs
            return [(lbl,evtScope ev (CoarseSchedule (InhAdd (pure (ev,li),xp)) Local $ pure li))]

fine_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(Conc evt, NewLabel lbl, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr'' (schedule_parser p2 ev) xs
            return [(lbl,evtScope ev (FineSchedule (InhAdd (pure (ev,li),xp)) Local $ pure li))]

        -------------------------
        --  Theory Properties  --
        -------------------------

parseExpr' :: (HasMchExpr b a, Ord label)
           => Lens' MachineP3 (Map label a) 
           -> [(label,b)] 
           -> RWS () [Error] MachineP3 ()
parseExpr' ln xs = modify $ ln %~ M.union (M.fromList $ map (second $ view mchExpr) xs)

instance IsExprScope Axiom where
    toNewEvtExprDefault _ _ = return []
    toMchExpr _ _    = return []
    toThyExpr lbl x  = return [Right $ PAssumptions lbl $ x^.mchExpr]
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

assumption :: MPipeline MachineP2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li <- ask
            xp <- parse_expr'' (p2^.pCtxSynt) xs
            return [(lbl,makeCell $ Axiom xp Local li)]

        --------------------------
        --  Program properties  --
        --------------------------

initialization :: MPipeline MachineP2
                    [(Label,ExprScope)]
initialization = machineCmd "\\initialization" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li <- ask
            xp <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,makeCell $ Initially (InhAdd xp) Local li)]

makeEvtCell :: IsEvtExpr a => InitOrEvent -> a -> ExprScope
makeEvtCell evt exp = makeCell $ EventExpr $ singleton evt $ makeCell exp

default_schedule_decl :: Pipeline MM
                   (MMap MachineP2, Maybe (MMap [(Label, ExprScope)]))
                   (Maybe (MMap [(Label, ExprScope)]))
default_schedule_decl = arr $ \(p2,csch) -> 
        Just $ addDefSch <$> p2 <.> evtsWith csch  -- .traverse._CoarseSchedule._)
    where
        --asCell' = asCell :: Prism' ExprScope EventExpr
        addDefSch m evts = m^.pNewEvents.eEventId._Right.to (default_sch evts)
        evtsWith :: Maybe (Map MachineId [(Label, ExprScope)]) 
                 -> Map MachineId [(EventId, LineInfo)]
        evtsWith csch = csch^.traverse & traverse %~ rights.(traverse %~ _1 id).referencedEvents
        referencedEvents :: [(Label, ExprScope)] -> [(InitOrEvent,LineInfo)]
        referencedEvents m = m^.traverse._2._EventExpr'.withKey'.traverse.to (\(eid,s) -> (eid,) <$> s^.lineInfo.to setToList) -- _1.to (:[])
        li = LI "default" 1 1
        makeDelete (InhAdd x) = InhDelete (Just x)
        makeDelete (InhDelete x) = InhDelete x
        default_sch :: [(EventId, LineInfo)]
                    ->   EventId
                    -> [(Label, ExprScope)]
        default_sch evts e = case e `L.lookup` evts of
                Just _li -> map ((def,) . makeEvtCell (Right e)) [sch,sch']
                Nothing  -> map ((def,) . makeEvtCell (Right e)) [sch]
            where
                def  = label "default"
                sch  = CoarseSchedule (InhAdd (pure (e,li),zfalse)) Inherited $ pure li
                sch' = sch & inhStatus %~ makeDelete & declSource .~ Local

instance IsExprScope Invariant where
    toNewEvtExprDefault _ _ = return []
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

invariant :: MPipeline MachineP2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li <- ask
            xp <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,makeCell $ Invariant xp Local li)]

instance IsExprScope InvTheorem where
    toNewEvtExprDefault _ _ = return []
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

mch_theorem :: MPipeline MachineP2
                    [(Label,ExprScope)]
mch_theorem = machineCmd "\\theorem" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li <- ask
            xp <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,makeCell $ InvTheorem xp Local li)]

instance IsExprScope TransientProp where
    toNewEvtExprDefault _ _ = return []
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

transient_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transient_prop = machineCmd "\\transient" $ \(evts', NewLabel lbl, Expr xs) _m p2 -> do
            let evts = map (as_label.getConcrete) evts'
                _ = evts' :: [Conc EventId]
            es   <- get_events p2 
                   =<< bind "Expecting at least one event" (NE.nonEmpty evts)
            li   <- ask
            tr   <- parse_expr''
                    (p2^.pMchSynt & free_dummies .~ True) 
                    xs
            let withInd = L.filter (not . M.null . (^. eIndices) . ((p2 ^. pEvents) !)) (NE.toList es)
            toEither $ error_list 
                [ ( not $ L.null withInd
                  , [s|event(s) %s have indices and require witnesses|] 
                        $ intercalate "," $ map pretty withInd) ]
            let vs = used_var' tr
                fv = vs `M.intersection` (p2^.pDummyVars)
                prop = Tr fv tr es empty_hint
            return [(lbl,makeCell $ TransientProp prop Local li)]

transientB_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transientB_prop = machineCmd "\\transientB" $ \(evts', NewLabel lbl, PlainText hint, Expr xs) _m p2 -> do
            let evts = map (as_label.getConcrete) evts'
                _  = evts' :: [Conc EventId]
            es   <- get_events p2 
                    =<< bind "Expecting at least one event" (NE.nonEmpty evts)
            li   <- ask
            tr   <- parse_expr''
                    (p2^.pMchSynt & free_dummies .~ True) 
                    xs
            let fv = free_vars' ds tr
                ds = p2^.pDummyVars
            evts' <- bind "Expecting non-empty list of events"
                    $ NE.nonEmpty evts
            hint  <- tr_hint p2 fv evts' hint
            let prop = transientProp p2 tr es hint
            return [(lbl,makeCell $ TransientProp prop Local li)]

instance IsExprScope ConstraintProp where
    toNewEvtExprDefault _ _ = return []
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

constraint_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
constraint_prop = machineCmd "\\constraint" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li  <- ask
            pre <- parse_expr''
                    (p2^.pMchSynt
                        & free_dummies .~ True
                        & is_step .~ True)
                    xs
            let vars = elems $ free_vars' ds pre
                ds = p2^.pDummyVars
                prop = Co vars pre
            return [(lbl,makeCell $ ConstraintProp prop Local li)]

instance IsExprScope SafetyDecl where
    toNewEvtExprDefault _ _ = return []
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

safety_prop :: Label
            -> StringLi
            -> StringLi
            -> MachineId
            -> MachineP2
            -> M [(Label,ExprScope)]
safety_prop lbl pCt qCt _m p2 = do
            li <- ask
            p <- unfail $ parse_expr''
                    (p2^.pMchSynt & free_dummies .~ True) 
                    pCt
            q <- unfail $ parse_expr''
                    (p2^.pMchSynt & free_dummies .~ True) 
                    qCt
            p <- trigger p
            q <- trigger q
            let new_prop = unlessProp p2 p q
            return [(lbl,makeCell $ SafetyProp new_prop Local li)]

safetyA_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
safetyA_prop = machineCmd "\\safety" 
                $ \(NewLabel lbl, Expr pCt, Expr qCt) -> safety_prop lbl pCt qCt

safetyB_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
safetyB_prop = machineCmd "\\safetyB" 
                $ \(NewLabel lbl, evt, Expr pCt, Expr qCt) _ _ -> do
    let _ = safety_prop lbl pCt qCt
        _ = evt :: Abs EventId
    bind "OBSOLETE FEATURE: p UNLESS q EXCEPT evt is no longer supported" Nothing

instance IsExprScope ProgressDecl where
    toNewEvtExprDefault _ _ = return []
    toMchExpr lbl e = return [Right $ PProgress (PId lbl) $ e^.mchExpr]
    toThyExpr _ _   = return []
    toNewPropSet lbl x = return $ if x^.declSource == Local 
            then [Right $ Progress (PId lbl) $ x^.mchExpr] 
            else []
    toOldPropSet lbl x = return $ if x^.declSource == Inherited 
            then [Right $ Progress (PId lbl) $ x^.mchExpr] 
            else []
    toNewEvtExpr _ _ = return []
    toOldEvtExpr _ _ = return []

transientProp :: (HasTheoryP2 p,HasExpr expr)
              => p -> expr 
              -> NonEmpty EventId 
              -> TrHint' expr 
              -> Transient' expr
transientProp p2 p = Tr dum p
    where
        ds  = p2^.pDummyVars
        dum = free_vars' ds p

unlessProp :: (HasTheoryP2 p,HasExpr expr)
           => p -> expr -> expr -> SafetyProp' expr
unlessProp p2 p q = Unless (M.elems dum) p q
    where
        ds  = p2^.pDummyVars
        dum = free_vars' ds p `union` free_vars' ds q

leadsTo :: (HasTheoryP2 p,HasExpr expr)
        => p -> expr -> expr -> ProgressProp' expr
leadsTo p2 p q = LeadsTo (M.elems dum) p q
    where
        ds  = p2^.pDummyVars
        dum = free_vars' ds p `union` free_vars' ds q

progress_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
progress_prop = machineCmd "\\progress" $ \(NewLabel lbl, Expr pCt, Expr qCt) _m p2 -> do
            li <- ask
            p    <- unfail $ parse_expr''
                    (p2^.pMchSynt & free_dummies .~ True)
                    pCt
            q    <- unfail $ parse_expr''
                    (p2^.pMchSynt & free_dummies .~ True)
                    qCt
            p  <- trigger p
            q  <- trigger q
            let new_prop = leadsTo p2 p q
            return [(lbl,makeCell $ ProgressProp new_prop Local li)]

instance IsEvtExpr IndexWitness where
    defaultEvtWitness _ _ = return []
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr Old evt _ w
        | w^.declSource == Local = return [Right (evt,[EIndWitness (v^.name) (WitSuch v $ w^.evtExpr)])]
        | otherwise              = return []
        where v = w^.ES.var
    toEvtScopeExpr New _ _ _ = return []
    setSource _ _ x = x
    inheritedFrom _ = []

instance IsEvtExpr ParamWitness where
    defaultEvtWitness _ _ = return []
    toMchScopeExpr _ _ = return []
    toEvtScopeExpr New evt _ w
        | w^.declSource == Local = return [Right (evt,[EParamWitness (v^.name) (WitSuch v $ w^.evtExpr)])]
        | otherwise              = return []
        where v = w^.ES.var
    toEvtScopeExpr Old _ _ _ = return []
    setSource _ _ x = x
    inheritedFrom _ = []

instance IsEvtExpr ES.Witness where
    defaultEvtWitness _ _ = return []
    toMchScopeExpr _ w   
        | w^.declSource == Local = return [Right $ PInitWitness (v^.name) (WitSuch v $ w^.evtExpr)]
        | otherwise              = return []
        where v = w^.ES.var
    toEvtScopeExpr Old _ _ _ = return []
    toEvtScopeExpr New evt _ w
        | w^.declSource == Local = return [Right (evt,[EWitness (v^.name) (WitSuch v $ w^.evtExpr)])]
        | otherwise              = return []
        where v = w^.ES.var
    setSource _ _ x = x
    inheritedFrom _ = []

instance IsEvtExpr ActionDecl where
    defaultEvtWitness ev scope = case (scope^.inhStatus, scope^.declSource) of 
        (InhDelete (Just (_,act)),Local) -> do
            vs <- view pDelVars
            return [Right $ (ev,[EWitness (v^.name) (witnessOf v act) 
                                         | v <- M.elems $ frame' act `M.intersection` vs ])]
        _ -> return []
    toMchScopeExpr _ _  = return []
    toEvtScopeExpr scope eid lbl decl = do
            x <- parseEvtExpr'' "action"
                (uncurry M.union . (frame' &&& used_var'.ba_pred))
                (curry . lmap (_1 %~ setToNeList) . EActions) scope eid lbl decl
            return x

newtype Compose3 f g h a = Compose3 { getCompose3 :: f (g (h a)) }
    deriving (Functor)

instance (Applicative f,Applicative g,Applicative h) => Applicative (Compose3 f g h) where
    pure = Compose3 . pure.pure.pure
    Compose3 f <*> Compose3 x = Compose3 $ uncomp $ comp f <*> comp x
        where
            comp = Compose . Compose
            uncomp = getCompose . getCompose

_EventExpr' :: Prism' ExprScope (Map InitOrEvent EvtExprScope)
_EventExpr' = _ExprScope._Cell._EventExpr


instance IsExprScope EventExpr where
    toNewEvtExprDefault _ (EventExpr m) = 
          fmap (concat.M.elems) 
        $ M.traverseWithKey defaultEvtWitness 
        $ M.mapKeysMonotonic fromRight' 
        $ M.filterWithKey (const.isRight) m
    toMchExpr lbl (EventExpr m) = 
            fmap concat $ mapM (toMchScopeExpr lbl) $ M.elems 
                $ M.filterWithKey (const.isLeft) m
    toThyExpr _ _  = return []
    toNewPropSet _ _ = return []
    toOldPropSet _ _ = return []
    toNewEvtExpr lbl (EventExpr m) =
            fmap concat $ mapM g $ rights $ map f $ M.toList m
        where f (x,y) = (,y) <$> x
              g (x,y) = toEvtScopeExpr New x lbl y
    toOldEvtExpr lbl (EventExpr m) = do
            concat <$> mapM fields (rights $ map f $ M.toList m)
        where f (x,y) = (,y) <$> x
              fields :: (EventId, EvtExprScope)
                     -> Reader MachineP2 [Either Error (EventId, [EventP3Field])]
              fields (x,y) = toEvtScopeExpr Old x lbl y

init_witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
init_witness_decl = machineCmd "\\initwitness" $ \(VarName var, Expr xp) _m p2 -> do
            -- ev <- get_event p2 evt
            li <- ask
            p  <- parse_expr'' (p2^.pMchSynt) xp
            v  <- bind ([s|'%s' is not a disappearing variable|] $ render var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            return [(label $ render var, makeEvtCell (Left InitEvent) (Witness v p Local $ pure li))]

event_parser :: HasMachineP2 phase => phase -> EventId -> ParserSetting
event_parser p2 ev = (p2 ^. pEvtSynt) ! ev

schedule_parser :: HasMachineP2 phase => phase -> EventId -> ParserSetting
schedule_parser p2 ev = (p2 ^. pSchSynt) ! ev

machine_events :: HasMachineP1 phase => phase -> Map Label EventId
machine_events p2 = L.view pEventIds p2

evtScope :: IsEvtExpr a => EventId -> a -> ExprScope
evtScope ev x = makeCell $ EventExpr $ M.singleton (Right ev) (makeCell x)

addEvtExpr :: IsEvtExpr a
           => W.WriterT [(UntypedExpr,[String])] M (EventId,[(UntypedExpr,[String])] -> a) 
           -> M ExprScope
addEvtExpr m = do
    ((ev,f),w) <- W.runWriterT m
    return $ evtScope ev (f w)

check_types :: Either [String] a -> M a    
check_types c = do
    li <- ask
    hoistEither $ either (\xs -> Left $ map (`Error` li) xs) Right c

defaultInitWitness :: MachineP2 -> [MachineP3'Field a b c] -> [MachineP3'Field a b c]
defaultInitWitness p2 xs = concatMap f xs ++ xs
    where
        vs = p2^.pDelVars
        f (PDelInits _lbl expr) = [PInitWitness (v^.name) (WitSuch v expr)
                                    | v <- M.elems $ used_var' expr `M.intersection` vs ]
        f _ = []

return []

check_props :: (PropName -> Property -> IO (a, Result))
            -> IO ([a], Bool)
check_props = $forAllProperties'

instance Arbitrary ExprScope where
    arbitrary = ExprScope <$> $(arbitraryCell' ''IsExprScope [ [t| ExprScope |] ])

instance Arbitrary EvtExprScope where
    arbitrary = do
        s <- $(arbitraryCell' ''IsEvtExpr [ [t| EvtExprScope |] ])
        return $ EvtExprScope s

instance Arbitrary EventExpr where
    arbitrary = EventExpr . fromList <$> listOf1 arbitrary
