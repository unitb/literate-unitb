{-# LANGUAGE TypeOperators
    , Arrows
    , TypeFamilies
    , OverloadedStrings
    , ViewPatterns
    #-}
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

import           Control.Monad 
import           Control.Monad.Reader.Class 
import           Control.Monad.Reader (Reader)
import           Control.Monad.State.Class 
import           Control.Monad.Writer.Class 
import           Control.Monad.Trans.RWS as RWS ( RWS )
import qualified Control.Monad.Writer as W

import Control.Precondition

import           Data.Either hiding (isLeft,isRight)
import           Data.Existential
import           Data.Functor.Compose
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.List.NonEmpty as NE
import           Data.Map.Class   as M hiding ( map, (\\) )
import qualified Data.Traversable   as T

import Test.QuickCheck hiding (label)

import Text.Printf.TH

import Utilities.Lens
import Utilities.Syntactic
import Utilities.Table

withHierarchy :: Pipeline MM (Hierarchy MachineId,MTable a) (MTable b)
              -> Pipeline MM (SystemP a) (SystemP b)
withHierarchy cmd = proc (SystemP ref tab) -> do
    tab' <- cmd -< (ref,tab)
    returnA -< SystemP ref tab'

run_phase3_exprs :: Pipeline MM SystemP2 SystemP3
run_phase3_exprs = 
        proc (SystemP ref tab) -> do
            es <- expressions -< tab
            x  <- liftP id -< wrapup ref tab es
            returnA -< SystemP ref x
    where
        err_msg :: Label -> String
        err_msg = [printf|Multiple expressions with the label %s|] . show
        wrapup :: Hierarchy MachineId
               -> MTable MachineP2 
               -> Maybe [Table MachineId [(Label, ExprScope)]]
               -> MM' Input (MTable MachineP3)
        wrapup r_ord p2 es = do
            let es' :: Maybe (MTable [(Label, ExprScope)])
                es' = inherit2 p2 r_ord . unionsWith (++) <$> es
            exprs <- triggerM
                =<< make_all_tables' err_msg
                =<< triggerM es'
            let _ = exprs :: MTable (Table Label ExprScope)
            xs <- T.sequence $ make_phase3 <$> p2 <.> exprs
            let mergeError (cevt,(e:es)) = unless (all (((e^.eActions) ==).view eActions) es) $ 
                    tell [MLError ([printf|event %s merges events with different action sets|] $ show cevt) []]
                mergeError (_,[]) = return ()
                merges :: [(EventId, [EventP3])]
                merges = xs^.traverse.pEventMerge'.withKey'.traverse.to ((:[]).second (L.map snd.snd))
            forM_ merges mergeError
            return xs
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

make_phase3 :: MachineP2 -> Table Label ExprScope -> MM' c MachineP3
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
            let _ = m :: Table SkipOrEvent [EventP3Field]
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
            let frame = M.ascElems $ (p2^.pStateVars) `M.difference` (p2^.pAbstractVars)
                act = BcmSuchThat frame pred
            li <- ask
            return [(lbl,evtScope ev (Action (InhAdd (ev NE.:| [],act)) Local $ pure li))]

bcmeq_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmeq_assgn = machineCmd "\\evbcmeq" $ \(Conc evt, NewLabel lbl, VarName v, Expr xs) _m p2 -> do
            let _ = lbl :: Label
            ev <- get_event p2 $ as_label (evt :: EventId)
            var@(Var _ t) <- bind
                ([printf|variable '%s' undeclared|] $ render v)
                $ v `M.lookup` (p2^.pStateVars)
            li <- ask
            xp <- parse_expr''
                (event_parser p2 ev & expected_type .~ Just t)
                xs
            check_types
                $ Right (Word var :: RawExpr) `mzeq` Right (asExpr xp)
            let act = Assign var xp
            return [(lbl,evtScope ev (Action (InhAdd (ev NE.:| [],act)) Local $ pure li))]

bcmsuch_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmsuch_assgn = machineCmd "\\evbcmsuch" $ \(Conc evt, NewLabel lbl, vs, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr''
                    (event_parser p2 ev & is_step .~ True)
                    xs
            vars <- bind_all (map getVarName vs)
                ([printf|variable '%s' undeclared|] . render)
                $ (`M.lookup` (p2^.pStateVars))
            let act = BcmSuchThat vars xp
            return [(lbl,evtScope ev (Action (InhAdd (ev NE.:| [],act)) Local $ pure li))]

bcmin_assgn :: MPipeline MachineP2
                    [(Label,ExprScope)]
bcmin_assgn = machineCmd "\\evbcmin" $ \(Conc evt, NewLabel lbl, VarName v, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            var@(Var _ t) <- bind
                ([printf|variable '%s' undeclared|] $ render v)
                $ v `M.lookup` (p2^.pStateVars)
            li  <- ask
            xp <- parse_expr''
                    (event_parser p2 ev & expected_type .~ Just (set_type t) )
                    xs
            let act = BcmIn var xp
            check_types $ Right (Word var) `zelem` Right (asExpr xp)
            return [(lbl,evtScope ev (Action (InhAdd (ev NE.:| [],act)) Local $ pure li))]

remove_init :: MPipeline MachineP2 [(Label,ExprScope)]
remove_init = machineCmd "\\removeinit" $ \(Identity lbls) _m _p2 -> do
            li <- ask
            return [(lbl,makeCell $ Initially (InhDelete Nothing) Local li) | Abs (InitLbl lbl) <- lbls ]

remove_assgn :: MPipeline MachineP2 [(Label,ExprScope)]
remove_assgn = machineCmd "\\removeact" $ \(Conc evt, lbls) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            return [(lbl,evtScope ev (Action (InhDelete Nothing) Local $ pure li)) | Abs (ActionLbl lbl) <- lbls ]

witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
witness_decl = machineCmd "\\witness" $ \(Conc evt, VarName var, Expr xp) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            let disappear  = (True,) <$> (p2^.pAbstractVars) `M.difference` (p2^.pStateVars)
                newIndices = (False,) <$> p2^.evtMergeAdded ev eIndices
            p  <- parse_expr'' (event_parser p2 ev & is_step .~ True) xp
            (isVar,v)  <- bind 
                ([printf|'%s' is not a disappearing variable or a new index|] (render var))
                (var `M.lookup` (disappear `M.union` newIndices))
            return $ if isVar
                then [(label $ render var,evtScope ev (Witness v p Local $ pure li))]
                else [(label $ render var,evtScope ev (IndexWitness v p Local $ pure li))]

guard_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
guard_decl = machineCmd "\\evguard" $ \(Conc evt, NewLabel lbl, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr'' (event_parser p2 ev) xs
            return [(lbl,evtScope ev (Guard (InhAdd (ev NE.:| [],xp)) Local $ pure li))]

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
            return [(lbl,evtScope ev (CoarseSchedule (InhAdd (ev NE.:| [],xp)) Local $ pure li))]

fine_sch_decl :: MPipeline MachineP2
                    [(Label,ExprScope)]
fine_sch_decl = machineCmd "\\fschedule" $ \(Conc evt, NewLabel lbl, Expr xs) _m p2 -> do
            ev <- get_event p2 $ as_label (evt :: EventId)
            li <- ask
            xp <- parse_expr'' (schedule_parser p2 ev) xs
            return [(lbl,evtScope ev (FineSchedule (InhAdd (ev NE.:| [],xp)) Local $ pure li))]

        -------------------------
        --  Theory Properties  --
        -------------------------

parseExpr' :: (HasMchExpr b a, IsKey Table label)
           => Lens' MachineP3 (Table label a) 
           -> [(label,b)] 
           -> RWS () [Error] MachineP3 ()
parseExpr' ln xs = modify $ ln %~ M.union (M.fromList $ map (second $ view mchExpr) xs)

assumption :: MPipeline MachineP2
                    [(Label,ExprScope)]
assumption = machineCmd "\\assumption" $ \(NewLabel lbl,Expr xs) _m p2 -> do
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
                   (MTable MachineP2, Maybe (MTable [(Label, ExprScope)]))
                   (Maybe (MTable [(Label, ExprScope)]))
default_schedule_decl = arr $ \(p2,csch) -> 
        Just $ addDefSch <$> p2 <.> evtsWith csch  -- .traverse._CoarseSchedule._)
    where
        --asCell' = asCell :: Prism' ExprScope EventExpr
        addDefSch m evts = m^.pNewEvents.eEventId._Right.to (default_sch evts)
        evtsWith csch = csch^.traverse & traverse %~ rights.referencedEvents
        referencedEvents :: [(Label, ExprScope)] -> [InitOrEvent]
        referencedEvents m = m^.traverse._2._EventExpr'.withKey'.traverse._1.to (:[]) -- .secondL _CoarseSchedule'._ -- _1.to (:[])
        li = LI "default" 1 1
        makeDelete (InhAdd x) = InhDelete (Just x)
        makeDelete (InhDelete x) = InhDelete x
        default_sch evts e 
                | e `elem` evts = map ((def,) . makeEvtCell (Right e)) [sch,sch']
                | otherwise     = map ((def,) . makeEvtCell (Right e)) [sch]
            where
                def  = label "default"
                sch  = CoarseSchedule (InhAdd (e NE.:| [],zfalse)) Inherited $ pure li
                sch' = sch & inhStatus %~ makeDelete & declSource .~ Local

invariant :: MPipeline MachineP2
                    [(Label,ExprScope)]
invariant = machineCmd "\\invariant" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li <- ask
            xp <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,makeCell $ Invariant xp Local li)]

mch_theorem :: MPipeline MachineP2
                    [(Label,ExprScope)]
mch_theorem = machineCmd "\\theorem" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li <- ask
            xp <- parse_expr'' (p2^.pMchSynt) xs
            return [(lbl,makeCell $ InvTheorem xp Local li)]

transient_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
transient_prop = machineCmd "\\transient" $ \(evts', NewLabel lbl, Expr xs) _m p2 -> do
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
                  , [printf|event(s) %s have indices and require witnesses|] 
                        $ intercalate "," $ map show withInd) ]
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

constraint_prop :: MPipeline MachineP2
                    [(Label,ExprScope)]
constraint_prop = machineCmd "\\constraint" $ \(NewLabel lbl,Expr xs) _m p2 -> do
            li  <- ask
            pre <- parse_expr''
                    (p2^.pMchSynt
                        & free_dummies .~ True
                        & is_step .~ True)
                    xs
            let vars = ascElems $ free_vars' ds pre
                ds = p2^.pDummyVars
                prop = Co vars pre
            return [(lbl,makeCell $ ConstraintProp prop Local li)]

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
            return [(lbl,makeCell $ SafetyProp new_prop Local li)]

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
unlessProp p2 p q = Unless (M.ascElems dum) p q
    where
        ds  = p2^.pDummyVars
        dum = free_vars' ds p `union` free_vars' ds q

leadsTo :: (HasTheoryP2 p,HasExpr expr)
        => p -> expr -> expr -> ProgressProp' expr
leadsTo p2 p q = LeadsTo (M.ascElems dum) p q
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

newtype Compose3 f g h a = Compose3 { getCompose3 :: f (g (h a)) }
    deriving (Functor)

instance (Applicative f,Applicative g,Applicative h) => Applicative (Compose3 f g h) where
    pure = Compose3 . pure.pure.pure
    Compose3 f <*> Compose3 x = Compose3 $ uncomp $ comp f <*> comp x
        where
            comp = Compose . Compose
            uncomp = getCompose . getCompose

_EventExpr' :: Prism' ExprScope (Table InitOrEvent EvtExprScope)
_EventExpr' = _ExprScope._Cell._EventExpr

_CoarseSchedule' :: Traversal' EvtExprScope (EventInhStatus Expr, DeclSource, NonEmpty LineInfo)
_CoarseSchedule' = _EvtExprScope._Cell._CoarseSchedule

init_witness_decl :: MPipeline MachineP2 [(Label,ExprScope)]
init_witness_decl = machineCmd "\\initwitness" $ \(VarName var, Expr xp) _m p2 -> do
            -- ev <- get_event p2 evt
            li <- ask
            p  <- parse_expr'' (p2^.pMchSynt) xp
            v  <- bind ([printf|'%s' is not a disappearing variable|] $ render var)
                (var `M.lookup` (L.view pAbstractVars p2 `M.difference` L.view pStateVars p2))
            return [(label $ render var, makeEvtCell (Left InitEvent) (Witness v p Local $ pure li))]

event_parser :: HasMachineP2 phase => phase -> EventId -> ParserSetting
event_parser p2 ev = (p2 ^. pEvtSynt) ! ev

schedule_parser :: HasMachineP2 phase => phase -> EventId -> ParserSetting
schedule_parser p2 ev = (p2 ^. pSchSynt) ! ev

machine_events :: HasMachineP1 phase => phase -> Table Label EventId
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
        f (PDelInits _lbl expr) = [PInitWitness (v^.name) (v, expr)
                                    | v <- M.ascElems $ used_var' expr `M.intersection` vs ]
        f _ = []

return []

check_props :: IO Bool
check_props = $quickCheckAll
