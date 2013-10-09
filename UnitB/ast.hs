{-# LANGUAGE DeriveDataTypeable, ExistentialQuantification #-} 
module UnitB.AST 
    ( Label
    , label
    , composite_label
    , Theory  (..)
    , Machine (..)
    , Event   (..)
    , empty_event
    , empty_machine
    , empty_theory
    , Transient   (..)
    , Constraint  (..)
    , ProgressProp(..)
    , Schedule    (..)
    , SafetyProp  (..) 
    , PropertySet (..) 
    , empty_property_set
    , Rule (..)
    , Variant (..)
    , variant_decreased
    , variant_equals_dummy
    , variant_bounded
    , Direction (..)
    , RefRule (..)
    , primed, make_unique
    , merge_struct
    , merge_import
    , merge_decl
    , merge_exprs
    , merge_proofs
    , all_types
    , basic_theory
    , disjoint_union
    , cycles
    , ScheduleChange 
        ( add, remove
        , keep, event
        , rule)
    , replace, weaken
    , ScheduleRule (..)
    , list_schedules
    , default_schedule
    ) 
where
 
    -- Modules
import UnitB.SetTheory
import UnitB.Theory
import UnitB.Calculation
import UnitB.Label

import Z3.Z3 hiding (merge)

    -- Libraries
import Control.Applicative ( (<|>) )
import Control.Monad hiding ( guard )
import Control.Monad.Writer hiding ( guard )

import           Data.Function
import           Data.Graph
import           Data.List as L hiding ( union, inits )
import           Data.Map as M hiding (map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Typeable

import Utilities.Format

basic_theory = Theory []
    (symbol_table [set_sort,fun_sort,BoolSort,IntSort,RealSort]) empty empty empty empty

all_types th = unions (types th : map all_types (extends th)) 

empty_theory :: Theory
empty_theory = Theory [] 
    empty empty empty empty empty

data Event = Event 
        { indices   :: Map String Var
        , sched_ref :: Map Int ScheduleChange
        , c_sched   :: Map Label Expr
        , f_sched   :: Maybe Expr
        , params    :: Map String Var
        , guard     :: Map Label Expr
        , action    :: Map Label Expr }
    deriving Show

empty_event = Event empty empty default_schedule Nothing empty empty empty

data Machine = 
    Mch 
        { _name      :: Label
        , theory     :: Theory
        , variables  :: Map String Var
        , inits      :: Map Label Expr
        , events     :: Map Label Event
        , inh_props  :: PropertySet
        , props      :: PropertySet }
    deriving (Show, Typeable)

class Show a => RefRule a where
    refinement_po :: a -> Machine -> Map Label ProofObligation
    rule_name     :: a -> Label
    
empty_machine :: String -> Machine
empty_machine n = Mch (Lbl n) 
        empty_theory { extends = [basic_theory] }
        empty empty empty 
        empty_property_set 
        empty_property_set

merge :: (Eq c, Ord a, Monoid c) 
      => b -> (b -> b -> Either c b) 
      -> Map a b -> Map a b 
      -> Either c (Map a b)
merge x f m0 m1 = do
        xs <- toEither $ forM (toList m3) $ \(x,z) ->
            fromEither (x,z) $
                case M.lookup x m0 of
                    Just y  -> do
                        y <- f y z
                        return (x,y)
                    Nothing -> do
                        return (x,z)
        return $ fromList xs
    where
        m2 = M.map (const x) m0
        m3 = m1 `union` m2

toEither :: (Eq a, Monoid a) => Writer a b -> Either a b
toEither m
        | w == mempty   = Right x
        | otherwise     = Left w
    where
        (x,w) = runWriter m

fromEither :: Monoid a => b -> Either a b -> Writer a b
fromEither _ (Right y) = return y
fromEither x (Left y)  = do
        tell y
        return x    

disjoint_union :: (Monoid c, Eq c, Ord a) => (a -> c) -> Map a b -> Map a b -> Either c (Map a b)
disjoint_union f x y = do
        toEither $ forM_ zs $ \z ->
            tell $ f z
        return (x `union` y)
    where
        zs = S.toList (keysSet x `S.intersection` keysSet y)

merge_struct :: Machine -> Machine -> Either [String] Machine
merge_struct m0 m1 = toEither $ do
        th   <- fromEither empty_theory $ merge_th_types
                    (theory m0)
                    (theory m1) 
        evts <- fromEither empty $ merge 
                    (skip m1)
                    merge_evt_struct 
                    (events m0)
                    (events m1)
        return m0 
            { theory = th
            , events = evts
            }

merge_import m0 m1 = toEither $ do
        th   <- fromEither empty_theory $ merge_th_struct
                    (theory m0)
                    (theory m1) 
        return m0
            { theory = th }

merge_decl :: Machine -> Machine -> Either [String] Machine
merge_decl m0 m1 = toEither $ do
        th   <- fromEither empty_theory $ merge_th_decl
                    (theory m0)
                    (theory m1) 
        vars <- fromEither empty $ disjoint_union
                    (\x -> ["Name clash with variable '" ++ x ++ "'"])
                    (variables m0)
                    (variables m1)
        evts <- fromEither empty $ merge 
                    (skip m1)
                    merge_evt_decl
                    (events m0)
                    (events m1)
        return m0
                { theory = th
                , variables = vars
                , events = evts
                }

merge_exprs :: Machine -> Machine -> Either [String] Machine
merge_exprs m0 m1 = toEither $ do
        th   <- fromEither empty_theory $ merge_th_exprs
                    (theory m0)
                    (theory m1) 
        init <- fromEither empty $ disjoint_union 
                    (\x -> ["Name clash with initialization predicate '" ++ show x ++ "'"])
                    (inits m0)
                    (inits m1)
        evts <- fromEither empty $ merge 
                    (skip m1)
                    merge_evt_exprs
                    (events m0)
                    (events m1)
        inh   <- fromEither empty_property_set 
                $ ps_union_expr (inh_props m0) (inh_props m1)
        inh   <- fromEither empty_property_set 
                $ ps_union_expr inh $ props m1
--        inh   <- fromEither empty_property_set 
--                $ foldM ps_union_expr empty_property_set
--                    [ inh_props m0
--                    , inh_props m1
--                    , props m1 ]
        return m0
            { theory = th
            , inits = init
            , events = evts
            , inh_props = inh
            }

merge_proofs :: Machine -> Machine -> Either [String] Machine
merge_proofs m0 m1 = toEither $ do
        evts <- fromEither empty $ merge 
                    (skip m1)
                    merge_evt_proof
                    (events m0)
                    (events m1)
        inh   <- fromEither empty_property_set 
                $ ps_union_proofs (inh_props m0) (inh_props m1)
        inh   <- fromEither empty_property_set 
                $ ps_union_proofs inh $ props m1
--        inh   <- fromEither empty_property_set 
--                $ foldM ps_union_proofs empty_property_set
--                    [ inh_props m0
--                    , inh_props m1
--                    , props m1 ]
        unless (inv (inh_props m0) `isSubmapOf` inv inh) 
            $ tell ["incorrect inheritance"]
        return m0
            { inh_props = inh
            , events = evts
            }

merge_th_types :: Theory -> Theory -> Either [String] Theory
merge_th_types t0 t1 = toEither $ do
        let es = extends t0 ++ extends t1
        types <- fromEither empty $ disjoint_union
                (\x -> ["Name clash with type '" ++ show x ++ "'"])
                (types t0)
                (types t1)
        return $ t0
            { extends = es
            , types = types
            }
merge_th_decl :: Theory -> Theory -> Either [String] Theory
merge_th_decl t0 t1 = toEither $ do
        funs <- fromEither empty $ disjoint_union
                (\x -> ["Name clash with function '" ++ x ++ "'"])
                (funs t0)
                (funs t1)
        consts <- fromEither empty $ disjoint_union
                (\x -> ["Name clash with constant '" ++ x ++ "'"])
                (consts t0)
                (consts t1)
        dummies <- fromEither empty $ disjoint_union
                (\x -> ["Name clash with dummy '" ++ x ++ "'"])
                (dummies t0)
                (dummies t1)
        return $ t0
            { funs = funs
            , dummies = dummies
            , consts = consts
            }
merge_th_struct :: Theory -> Theory -> Either [String] Theory
merge_th_struct t0 t1 = toEither $ do
        let ext = (extends t0 ++ extends t1)
        return t0
            { extends = ext }
merge_th_exprs :: Theory -> Theory -> Either [String] Theory
merge_th_exprs t0 t1 = toEither $ do
        fact <- fromEither empty $ disjoint_union
                (\x -> ["Name clash with fact '" ++ show x ++ "'"])
                (fact t0)
                (fact t1)
        return $ t0
            { fact = fact }

merge_evt_struct :: Event -> Event -> Either [String] Event
merge_evt_struct e0 _ = return e0
merge_evt_decl :: Event -> Event -> Either [String] Event
merge_evt_decl e0 e1 = toEither $ do
        ind <- fromEither empty $ disjoint_union
                (\x -> ["multiple indices with the same name: " ++ x ++ ""])
                (indices e0)
                (indices e1)
        prm <- fromEither empty $ disjoint_union
                (\x -> ["multiple indices with the same name: " ++ x ++ ""])
                (params e0)
                (params e1)
        return e0 
            { indices = ind
            , params = prm }
merge_evt_exprs :: Event -> Event -> Either [String] Event
merge_evt_exprs e0 e1 = toEither $ do
        coarse_sch <- fromEither default_schedule $ do
                cs <- foldM (\x y -> do
                        disjoint_union (\x -> ["Two schedules have the same name: " ++ show x]) x y
                    ) default_schedule
                    [ c_sched e0 `difference` default_schedule
                    , c_sched e1 `difference` default_schedule]
                return cs
        let fine_sch   = f_sched e0 <|> f_sched e1
        grd <- fromEither empty $ disjoint_union
                (\x -> ["multiple guard with the same label: " ++ show x ++ ""])
                (guard e0)
                (guard e1)
        act <- fromEither empty $ disjoint_union
                (\x -> ["multiple actions with the same label: " ++ show x ++ ""])
                (action e0)
                (action e1)
        return e0 
            { c_sched = coarse_sch
            , f_sched = fine_sch
            , guard   = grd
            , action = act }

merge_evt_proof :: Event -> Event -> Either [String] Event
merge_evt_proof e0 e1 = toEither $ do
        ref <- fromEither empty $ disjoint_union
                (\x -> ["multiple schedule refinement rules with the same index: " ++ show x ++ ""])
                (sched_ref e0)
                (sched_ref e1)
        return e0 
            { sched_ref = ref }


--merge_theory :: Theory -> Theory -> Either [String] Theory
--merge_theory t0 t1 = toEither $ do
--        let es = extends t0 ++ extends t1
--        types <- fromEither empty $ disjoint_union
--                (\x -> ["Name clash with type '" ++ show x ++ "'"])
--                (types t0)
--                (types t1)
--        funs <- fromEither empty $ disjoint_union
--                (\x -> ["Name clash with function '" ++ show x ++ "'"])
--                (funs t0)
--                (funs t1)
--        consts <- fromEither empty $ disjoint_union
--                (\x -> ["Name clash with constant '" ++ show x ++ "'"])
--                (consts t0)
--                (consts t1)
--        fact <- fromEither empty $ disjoint_union
--                (\x -> ["Name clash with fact '" ++ show x ++ "'"])
--                (fact t0)
--                (fact t1)
--        dummies <- fromEither empty $ disjoint_union
--                (\x -> ["Name clash with dummy '" ++ show x ++ "'"])
--                (dummies t0)
--                (dummies t1)
--        return $ Theory es types funs consts fact dummies

skip m = Event 
        M.empty M.empty 
        default_schedule 
        Nothing M.empty 
        M.empty 
        $ fromList $ map f $ M.elems $ variables m
    where
        f v@(Var n _) = (label ("SKIP:" ++ n), Word v `zeq` primed (variables m) (Word v))

default_schedule = fromList [(label "default", zfalse)]

primed :: Map String Var -> Expr -> Expr
primed vs e = make_unique "@prime" vs e

make_unique :: String -> Map String Var -> Expr -> Expr
make_unique suf vs w@(Word (Var vn vt)) 
        | vn `M.member` vs    = Word (Var (vn ++ suf) vt)
        | otherwise           = w
make_unique _ _ c@(Const _ _ _)    = c
make_unique suf vs (FunApp f xs)     = FunApp f $ map (make_unique suf vs) xs
make_unique suf vs (Binder q d r xp) = Binder q d (f r) (f xp)
    where
        local = (L.foldr M.delete vs (map name d))
        f = make_unique suf local

instance Named Machine where
    name m = case _name m of Lbl s -> s

data Constraint = 
        Co [Var] Expr
    deriving Show

data Transient = 
        Transient 
            (Map String Var)    -- Free variables
            Expr                -- Predicate
            Label Int           -- Event, Schedule 
--            (Maybe Label)       -- Progress Property for fine schedule
--      | Grd thm
--      | Sch thm
    deriving Show

--data Derivation = Deriv 
--        Label Rule 
--        [LivenessDerivation] 
--        [Label] 

data Direction = Up | Down
    deriving Show

data Variant = 
--        SetVariant Var Expr Expr Direction
        IntegerVariant Var Expr Expr Direction
    deriving Show

--variant_equals_dummy (SetVariant d var _ _)     = Word d `zeq` var
variant_equals_dummy (IntegerVariant d var _ _) = Word d `zeq` var

--variant_decreased (SetVariant d var b Up)       = variant_decreased $ SetVariant d var b Down
variant_decreased (IntegerVariant d var _ Up)   = Word d `zless` var
--variant_decreased (SetVariant d var _ Down)     = error "set variants unavailable"
variant_decreased (IntegerVariant d var _ Down) = var `zless` Word d

--variant_bounded (SetVariant d var _ _)     = error "set variants unavailable"
variant_bounded (IntegerVariant _ var b Down) = b `zle` var
variant_bounded (IntegerVariant _ var b Up)   = var `zle` b

data Rule = forall r. RefRule r => Rule r

instance Show Rule where
    show (Rule x) = show x

--data Liveness = Live (Map Label ProgressProp) 

data Schedule = Schedule [Var] Expr Expr Label
    deriving Typeable

data ProgressProp = LeadsTo [Var] Expr Expr
    deriving Typeable

data SafetyProp = Unless [Var] Expr Expr
    deriving Typeable

instance Show ProgressProp where
    show (LeadsTo _ p q) = show p ++ "  |->  " ++ show q

instance Show SafetyProp where
    show (Unless _ p q) = show p ++ "  UNLESS  " ++ show q

data PropertySet = PS
        { transient    :: Map Label Transient
        , constraint   :: Map Label Constraint
        , inv          :: Map Label Expr       -- inv
        , inv_thm      :: Map Label Expr       -- inv thm
        , proofs       :: Map Label Proof
        , progress     :: Map Label ProgressProp
        , schedule     :: Map Label Schedule
        , safety       :: Map Label SafetyProp
        , derivation   :: Map Label Rule
        }

instance Show PropertySet where
    show x = intercalate ", " $ map (\(x,y) -> x ++ " = " ++ y)
        [ ("transient",  show $ transient x)
        , ("constraint", show $ constraint x)
        , ("inv", show $ inv x)
        , ("inv_thm", show $ inv_thm x)
        , ("proofs", show $ keys $ proofs x)
        , ("progress", show $ progress x)
        , ("safety", show $ safety x)
        , ("deduction steps", show $ derivation x)
        ]

data ScheduleChange = ScheduleChange 
        { event  :: Label
        , remove :: S.Set Label
        , add    :: S.Set Label
        , keep   :: S.Set Label
        , rule   :: ScheduleRule
        }
    deriving (Show)

data ScheduleRule = 
        Replace ProgressProp SafetyProp
        | Weaken
    deriving Show

weaken lbl = ScheduleChange lbl S.empty S.empty S.empty Weaken

replace lbl prog saf = ScheduleChange lbl S.empty S.empty S.empty (Replace prog saf)

list_schedules :: Map Int ScheduleChange -> Map Label Expr -> Map Int (Map Label Expr)
list_schedules r m0 = 
        fromAscList $ scanl f first (toAscList r)
    where
        p ref k _    = k `S.member` after ref 
        q ref k _    = not $ k `S.member` before ref 
        f (_,m1) (i,ref) = (i, M.filterWithKey (p ref) m0 `union` M.filterWithKey (q ref) m1)
        first_index
            | not $ M.null r = fst (findMin r)-1
            | otherwise      = 0
        first                = (first_index,fromList [(label "default",zfalse)])

before x = keep x `S.union` remove x
after x = keep x `S.union` add x

cycles xs = stronglyConnComp $ collapse $ sort $ alist ++ vs
    where
        f xs  = (fst $ head xs, fst $ head xs, map snd xs)
        vs    = map (\x -> (x,x,[])) $ nub (map fst xs ++ map snd xs)
        alist = map f $ groupBy ((==) `on` fst) $ sort xs
        collapse ( (x1,x2,xs) : zs@( (y1,_,ys):ws ) )
            | x1 == y1  = collapse $ (x1,x2,xs++ys):ws
            | x1 /= y1  = (x1,x2,xs) : collapse zs
        collapse xs = xs

--linearize :: [ScheduleChange] -> Either [[ScheduleChange]] [ScheduleChange]
--linearize xs = toEither $ mapM g comp
--    where
--        g (Node x []) = return $ vertex_fn x
--        g other@(Node x _) = do
--                tell [dec other []] 
--                return (vertex_fn x)
--          where
--            dec (Node v ts) vs = vertex_fn v : L.foldr dec vs ts        
--        comp     = scc graph
--        graph    = buildG (1,length xs) edges
--        pairs    = [ (x,y) | x <- vertices, y <- vertices, fst x /= fst y ]
--        vertex_fn x = fromList vertices ! x
--        vertices = zip [1..] xs
--        edges    = concatMap (uncurry f) pairs 
--        f (i,x) (j,y)
--            | S.null (after x `S.intersection` before y)    = []
--            | otherwise                                     = [(i,j)]
--
--first_schedule :: [ScheduleChange] -> S.Set Label -> S.Set Label
--first_schedule xs x = L.foldl f x $ reverse xs
--    where
--        f x y = (x `S.difference` after y) `S.union` before y
--
--all_schedules :: [ScheduleChange] -> S.Set Label -> [S.Set Label]
--all_schedules xs x = reverse $ L.foldl f [first_schedule xs x] xs
--    where
--        f xs@(x:_) y = ((x `S.difference` after y) `S.union` before y):xs

empty_property_set :: PropertySet
empty_property_set = PS 
        empty empty empty 
        empty empty empty 
        empty empty empty

ps_union_expr :: PropertySet -> PropertySet -> Either [String] PropertySet
ps_union_expr (PS a0 b0 c0 d0 e0 f0 i0 g0 h0) (PS a1 b1 c1 d1 _ f1 i1 g1 _) = 
    toEither $ do
        a2 <- fromEither empty $ disjoint_union (f "transient predicate") a0 a1
        b2 <- fromEither empty $ disjoint_union (f "co predicate") b0 b1
        c2 <- fromEither empty $ disjoint_union (f "invariant") c0 c1
        d2 <- fromEither empty $ disjoint_union (f "theorem") d0 d1
--        e2 <- fromEither empty $ disjoint_union (f "proof") e0 e1
        let e2 = e0
        f2 <- fromEither empty $ disjoint_union (f "progress property") f0 f1
        g2 <- fromEither empty $ disjoint_union (f "safety property") g0 g1
        i2 <- fromEither empty $ disjoint_union (f "schedule") i0 i1
        return $ PS a2 b2 c2 d2 e2 f2 i2 g2 h0
    where
        f n x = [format "Name clash for {0} '{1}'" (n :: String) x]         

ps_union_proofs :: PropertySet -> PropertySet -> Either [String] PropertySet
--ps_union_proofs (PS a0 b0 c0 d0 e0 f0 i0 g0 h0) (PS a1 b1 c1 d1 e1 f1 i1 g1 h1) = 
ps_union_proofs (PS a0 b0 c0 d0 e0 f0 i0 g0 h0) (PS _ _ _ _ _ _ _ _ h1) = 
    toEither $ do
        h2 <- fromEither empty $ disjoint_union (f "deduction step") h0 h1
        return $ PS a0 b0 c0 d0 e0 f0 i0 g0 h2
    where
        f n x = [format "Name clash for {0} '{1}'" (n :: String) x]         


composite_label xs = Lbl $ intercalate "/" $ map str xs
    where
        str (Lbl s) = s