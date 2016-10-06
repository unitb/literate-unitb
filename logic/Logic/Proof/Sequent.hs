{-# LANGUAGE TypeOperators
    , TypeFamilies #-}
module Logic.Proof.Sequent where

    -- Modules
import Logic.Expr
import Logic.Operator

    -- Libraries
import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding (Context,elements)
import Control.Lens.Extras
import Control.Lens.HierarchyTH
import Control.Monad.RWS
import Control.Precondition

import Data.Char
import Data.Default
import Data.List as L
import Data.List.Ordered as L
import Data.Map.Class    as M hiding ( map, Unordered )
import Data.Maybe  as MM hiding (fromJust)
import Data.PartialOrd
import qualified Data.Set  as S
import Data.Serialize hiding (label,Partial)
import Data.String.Lines
import Data.Typeable
import Data.Word

import GHC.Generics.Instances

import Test.QuickCheck.Report ()
import Test.QuickCheck hiding (label)
import Test.QuickCheck.ZoomEq

import Text.Printf.TH

import Utilities.Table

type Sequent = AbsSequent GenericType HOQuantifier

type Sequent' = GenSequent InternalName GenericType FOQuantifier Expr'

type HOSequent expr = GenSequent Name GenericType HOQuantifier expr

type FOSequent = GenSequent InternalName FOType FOQuantifier FOExpr

type AbsSequent t q = GenSequent Name t q (AbsExpr Name t q)

data SyntacticProp = SyntacticProp  
        { _associative  :: Table Name ExprP
        , _monotonicity :: Map (Relation,Function) (ArgDep Rel) }
            -- (rel,fun) --> rel
    deriving (Eq,Show,Generic)

preserve :: Fun -> [Function] -> [((Relation,Function),ArgDep Rel)]
preserve op funs = [((view name op,f),Independent $ Rel op Direct) | f <- funs ]

type Function = Name

type Relation = Name

data Rel = Rel Fun Flipping
    deriving (Eq,Show,Generic,Typeable)

data ArgDep a = Side (Maybe a) (Maybe a) | Independent a
    deriving (Eq,Generic,Show,Typeable)

data ArgumentPos = RightArg | LeftArg | MiddleArg
    deriving (Show)

data GenSequent name t q expr = Sequent 
        { _genSequentTimeout  :: Word32
        , _genSequentResource :: Word32
        , _genSequentContext  :: GenContext name t q
        , _genSequentSyntacticThm :: SyntacticProp
        , _genSequentNameless :: [expr] 
        , _genSequentNamed :: Table Label expr
        , _genSequentGoal  :: expr }
    deriving (Eq, Generic, Show, Functor, Foldable, Traversable)

-- class HasGoal a b | a -> b where
--     goal :: Getter a b

makeFields ''GenSequent
makeLenses ''GenSequent
makeClassy ''SyntacticProp
mkCons ''SyntacticProp

applyTimeout :: RealFrac d
             => Maybe d
             -> GenSequent n t q expr
             -> GenSequent n t q expr
applyTimeout x' = timeout %~ round . f . fromIntegral
    where
        x = fromMaybe 1 x'
        f y = x * y

instance (Ord name,Eq t,Eq q,Ord expr) => 
        PreOrd (GenSequent name t q expr) where
    partCompare x y = genericPreorder (f x) (f y)
        where
            f (Sequent to r ctx sThm hyps0 hyps1 goal) = 
                    ( Partial to,Partial r,ctx,sThm
                    , Unordered hyps0,hyps1,Quotient goal)

instance (Ord name,Eq t,Eq q,Ord expr) => 
        PartialOrd (GenSequent name t q expr) where

instance PreOrd SyntacticProp where
    partCompare = genericPartialOrder

instance PartialOrd SyntacticProp where

instance ZoomEq SyntacticProp where
instance Default SyntacticProp where
    def = empty_monotonicity

instance (Ord n,ZoomEq n,ZoomEq t,ZoomEq q,ZoomEq e) 
        => ZoomEq (GenSequent n t q e) where

instance HasExprs (GenSequent n t q e) e where
    traverseExprs f (Sequent tout res ctx prop hyp0 hyp1 g) = 
        Sequent tout res ctx prop 
                <$> traverse f hyp0 
                <*> traverse f hyp1 
                <*> f g

instance HasSorts (GenSequent n t q e) (Table Name Sort) where
    sorts = context.sorts

instance HasConstants (GenSequent n t q e) (Table n (AbsVar n t)) where
    constants = context.constants

predefined :: [InternalName]
predefined = map fromString''
             [ "=","union","and","or","=>","<=","<",">","^"
             , "subset","select","true","false"
             , "intersect","+","-","*","/","not"
             , "Just", "Nothing", "pair", "ite"
             , "empty-set", "store" ]

checkScopesAux :: Expr -> RWS Context [Expr] () ()
checkScopesAux e@(Word v) = do
    b0 <- views constants (M.lookup $ v^.name)
    b1 <- views definitions (M.member $ v^.name)
    b2 <- views functions (M.member $ v^.name)
    unless (b0 == Just v || b1 || b2) $ 
        tell [e]
checkScopesAux (Lit _ _) = return ()
checkScopesAux e@(FunApp fn args) = do
    b0 <- views functions (M.member $ fn^.name)
    b1 <- views definitions (M.member $ fn^.name)
    unless (b0 || b1 || ((z3_name fn) `elem` predefined)) 
        $ tell [e]
    mapM_ checkScopesAux args
checkScopesAux (Binder _ vs r t _) =
    local (over constants $ M.union $ symbol_table vs) $ do
        mapM_ checkScopesAux [r,t]
checkScopesAux (Cast _ e _) = do
    checkScopesAux e
checkScopesAux (Lift e _) = do
    checkScopesAux e
checkScopesAux (Record e _) = do
    mapMOf_ traverseRecExpr checkScopesAux e

makeSequent :: Pre
            => Context
            -> SyntacticProp
            -> [Expr]
            -> Table Label Expr
            -> Expr
            -> Sequent
makeSequent ctx props asms0 asms1 g = checkSequent $ 
    Sequent 3000 1 ctx props asms0 asms1 g

checkSequent :: Pre
             => Sequent -> Sequent
checkSequent s = byPred msg (const $ L.null xs) (Pretty s) s
    where
        msg = [printf|Sequent scopes: \n%s|] $ L.unlines $ map pretty_print' xs
        checkScopes' e = do
            xs <- snd <$> listen (checkScopesAux e)
            unless (L.null xs)
                $ tell [e]
        ctx = s^.context 
                & definitions %~ symbol_table 
                & constants %~ symbol_table
                & functions %~ symbol_table
                & dummies   %~ symbol_table
        travAsserts = traverseOf_ traverseExprs checkScopes' s
        checkDef (Def _ _ ts _ e) = local (constants %~ M.union (symbol_table ts)) $ checkScopes' e
        travDefs' [] = return ()
        travDefs' (x:xs) = do
                    checkDef x 
                    local (definitions %~ insert_symbol x) 
                          (travDefs' xs)
        travDefs  = local (definitions .~ M.empty) 
                $ travDefs' $ sortDefs $ ctx^.definitions
        xs :: [Expr]
        xs  = snd $ execRWS (travAsserts >> travDefs) ctx ()

expressions :: Getter (GenSequent n t q expr) [expr]
expressions = to $ \s -> (s^.goal) : (s^.nameless) ++ (M.ascElems $ s^.named)

leftMono :: ArgDep a -> Maybe a
leftMono (Side l _) = l
leftMono (Independent m) = Just m

rightMono :: ArgDep a -> Maybe a
rightMono (Side _ r) = r
rightMono (Independent m) = Just m

middleMono :: ArgDep a -> Maybe a
middleMono (Independent m) = Just m
middleMono _ = Nothing

isAssociative :: SyntacticProp -> Fun -> Maybe ExprP
isAssociative sp f = (f^.name) `M.lookup` (sp^.associative)

isMonotonic :: HasSyntacticProp m
            => m -> Relation -> Function 
            -> ArgumentPos -> Maybe (ExprP -> ExprP -> ExprP)
isMonotonic m rel fun pos = do
    r <- (rel,fun) `M.lookup` (m^.monotonicity)
    Rel rel fl <- case pos of
        LeftArg   -> leftMono r
        RightArg  -> rightMono r
        MiddleArg -> middleMono r
    case fl of 
        Direct -> 
            return $ typ_fun2 rel
        Flipped ->
            return $ flip $ typ_fun2 rel

instance HasGenContext (GenSequent n a b e) n a b where
    genContext = context

empty_monotonicity :: SyntacticProp
empty_monotonicity = makeSyntacticProp

instance Monoid SyntacticProp where
    mempty = genericMEmpty
    mconcat = genericMConcat
    mappend = genericMAppend

empty_sequent :: (TypeSystem2 t,IsQuantifier q,HasGenExpr expr) 
              => GenSequent n t q expr
empty_sequent = (Sequent 3000 1 empty_ctx empty_monotonicity [] M.empty ztrue)

instance (TypeSystem t, IsQuantifier q) => PrettyPrintable (AbsSequent t q) where
    pretty s = L.unlines $ asms ++ ["|----",goal'] 
        where
            indent n = over traverseLines (replicate n ' ' ++)
            indentAfter n = partsOf traverseLines %~ zipWith (++) ("" : repeat (replicate n ' '))
            asms   = map (indent 1) $ 
                    ["sort: " ++ intercalate ", " (L.filter (not.L.null) $ MM.mapMaybe f $ toList ss)]
                    ++ (map pretty $ ascElems fs)
                    ++ (map pretty $ sortDefs ds)
                    ++ (map pretty $ ascElems vs)
                    ++ map showWithLabel hs
                    ++ map pretty_print' hs'
            goal' = indent 1 $ pretty_print' g
            Context ss vs fs ds _ = s^.context
            hs  = map (_1 %~ (++":  ") . pretty) $ M.toList (s^.named)
            hs' = s^.nameless
            margin = maximum (0:map (length.fst) hs)
            showWithLabel (lbl,x) = take margin (lbl ++ repeat ' ') ++ indentAfter margin (pretty_print' x)
            g  = s^.goal
            f (_, IntSort)  = Nothing
            f (_, BoolSort) = Nothing
            f (_, RealSort) = Nothing
            f (_, RecordSort _) = Nothing
            f (x, Datatype args n _) = f (x, Sort n (asInternal n) $ length args)
            f (x, DefSort y z xs _)  = f (x, Sort y z $ length xs)
            f (_, Sort _ z 0) = Just $ render z
            f (_, Sort _ z n) = Just $ [printf|%s [%s]|] (render z) (intersperse ',' $ map chr $ take n [ord 'a' ..]) 

remove_type_vars :: Sequent' -> FOSequent
remove_type_vars (Sequent tout res ctx m asm hyp goal) = Sequent tout res ctx' m asm' hyp' goal'
    where
        (Context ss _ _ dd _) = ctx
        _ = dd :: Table InternalName Def'
        asm_types = MM.catMaybes 
                    $ map type_strip_generics 
                    $ S.elems $ S.unions 
                    $ map used_types $ map target (M.elems dd) ++ asm ++ M.elems hyp
        seq_types = S.fromList asm_types `S.union` used_types goal'
        -- seq_types = S.unions $ L.map referenced_types $ asm_types ++ S.toList (used_types goal')

        const_types :: [FOType]
        const_types = concatMap (universe.type_of) 
                        $ M.elems $ ctx'^.constants 
        decl_types :: S.Set FOType
        decl_types = S.unions $ map used_types $ goal' : asm' ++ M.elems hyp'
        ctx' :: FOContext
        ctx'  = to_fol_ctx decl_types $ ctx
                    & sorts %~ M.union records
        records = symbol_table $ nubSort $ 
                    (S.toList decl_types ++ const_types)^.partsOf (traverse.foldSorts.filtered (is _RecordSort))
        asm' :: [FOExpr]
        asm' = map snd $ concatMap (gen_to_fol seq_types (label "")) asm
        hyp' :: Table Label FOExpr
        hyp' = M.fromList $ concat $ M.elems $ M.mapWithKey (gen_to_fol seq_types) hyp
        goal' :: FOExpr
        goal' = vars_to_sorts ss goal

one_point :: (IsQuantifier q, TypeSystem2 t,IsName n) 
          => GenSequent n t q (AbsExpr n t q) 
          -> GenSequent n t q (AbsExpr n t q)
one_point s = s & goal .~ g'
                & nameless %~ asm
    where
        g = s^.goal
        asm
            | g == g'   = id
            | otherwise = (++ [znot g])
        g' = one_point_rule g

differs_by_one :: Eq a => [a] -> [a] -> Maybe (ArgumentPos,a,a)
differs_by_one xs ys = f $ zip ws $ zip xs ys
    where
        ws = LeftArg : replicate (n-2) MiddleArg ++ [RightArg]
        n = length xs
        f [] = Nothing
        f ((i,(x,y)):xs) 
            | x == y        = f xs
            | all (uncurry (==) . snd) xs = Just (i,x,y)
            | otherwise     = Nothing

flatten_assoc :: (IsAbsExpr expr,TypeT expr ~ Type) 
              => FunT expr -> [expr] -> [expr]
flatten_assoc fun xs = concatMap f xs
    where
        f (FunApp fun' xs)
            | fun == fun' = concatMap f xs
        f e = [e]

differs_by_segment :: Eq a => [a] -> [a] -> Maybe (ArgumentPos,[a],[a])
differs_by_segment xs ys
        | L.null ps && L.null qs = Nothing
        | L.null ps = Just (LeftArg,xs'',ys'')
        | L.null qs = Just (RightArg,xs'',ys'')
        | otherwise = Just (MiddleArg,xs'',ys'')
    where
        (ps,xs',ys')   = longestCommonPrefix xs ys
        (qs,xs'',ys'') = longestCommonSuffix xs' ys'

longestCommonPrefix :: Eq a => [a] -> [a] -> ([a],[a],[a])
longestCommonPrefix xs'@(x:xs) ys'@(y:ys)
        | x == y    = longestCommonPrefix xs ys & _1 %~ (x:)
        | otherwise = ([],xs',ys')
longestCommonPrefix xs ys = ([],xs,ys)

longestCommonSuffix :: Eq a => [a] -> [a] -> ([a],[a],[a])
longestCommonSuffix xs ys = longestCommonPrefix 
                                    (reverse xs) 
                                    (reverse ys) 
                                & each %~ reverse

apply_monotonicity :: Sequent -> Sequent
apply_monotonicity po = fromMaybe po $
        case g of
            Binder Forall (Var nam t:vs) rs ts _ -> do
                let v   = Var (fresh nam $ symbols ctx) t
                    g'
                        | L.null vs = rs `zimplies` ts
                        | otherwise = zforall vs rs ts
                return $ apply_monotonicity $ po' & constants %~ M.insert (view name v) v
                                                  & goal .~ rename nam (v^.name) g'
            FunApp f [lhs, rhs] ->
                case (lhs,rhs) of
                    (Binder Forall vs r0 t0 _, Binder Forall us r1 t1 _) 
                        | shared vs us && z3_name f `elem` [[smt|=|],[smt|=>|]] -> do
                            let vs0 = vs L.\\ us
                                vs1 = us L.\\ vs
                                vs' = L.intersect vs us
                            return $ apply_monotonicity $ 
                                po' & goal .~ 
                                    (zforall vs' ztrue $ 
                                        funApp f [zforall vs0 r0 t0, zforall vs1 r1 t1])
                    (Binder Exists vs r0 t0 _, Binder Exists us r1 t1 _) 
                        | shared vs us && z3_name f `elem` [[smt|=|],[smt|=>|]] -> do
                            let vs0 = vs L.\\ us
                                vs1 = us L.\\ vs
                                vs' = L.intersect vs us
                            return $ apply_monotonicity $
                                po' & goal .~ 
                                    (zforall vs' ztrue $ 
                                        funApp f [zexists vs0 r0 t0, zexists vs1 r1 t1])
                    (Binder q0 vs r0 t0 _, Binder q1 us r1 t1 _)
                        | q0 == q1 && vs == us 
                            && r0 == r1 && z3_name f == [smt|=|] -> 
                                return $ apply_monotonicity $
                                    po' & goal .~ (zforall vs r0 $ t0 `zeq` t1)
                        | q0 == q1 && vs == us 
                            && t0 == t1 && z3_name f == [smt|=|] -> 
                                return $ apply_monotonicity $
                                    po' & goal .~ (zforall vs ztrue $ r0 `zeq` r1)
                    (FunApp g0 xs, FunApp g1 ys)
                        | (length xs /= length ys && isNothing (isAssociative mm' g0))
                            || g0 /= g1 -> Nothing
                        | z3_name f == [smt|=|] -> do
                            (_,x,y) <- difference g0 xs ys
                            return $ apply_monotonicity $
                                po' & goal .~ funApp f [x, y]
                        | otherwise -> do
                                -- and(0,1), or(0,1), 
                                --      =>(1)       -> f.x => f.y -> x => y
                                -- not (0), =>(0)   -> f.x => f.y -> y => x
                                --   arithmetic relations are not implement
                                -- <=(0)            -> f.x => f.y -> y <= x
                                -- <=(1)            -> f.x => f.y -> x <= y
                                -- +(0,1),-(0)      -> f.x <= f.y -> x <= y
                                -- -(1)             -> f.x <= f.y -> y <= x
                                --   How would we treat the case of:
                                --   context => a+b+x R a+b+y
                                --   we need a means to distinguish an 
                                --   implication that introduces contextual
                                --   information
                            x <- mono (view name f) g0 xs ys
                            return $ apply_monotonicity $ po' & goal .~ x
--                            let op = name g0
--                                mono i xs
--                                    | (op `elem` [[smt|and|],[smt|or|]]) ||
--                                        (op == [smt|=>|] && i == 1)     = FunApp f xs
--                                    |  op == [smt|not|] ||
--                                        (op == [smt|=>|] && i == 0)     = FunApp f $ reverse xs
--                                    | otherwise                  = error $ "Z3.discharge': unexpected operator / position pair: " ++ op ++ ", " ++ show i
--                            in case differs_by_one xs ys of
--                                Just (i,x,y) -> 
--                                    apply_monotonicity (Sequent ctx asm h' $ 
--                                        mono i [x, y])
--                                Nothing -> 
--                                    po
                    _ -> Nothing
            _ -> Nothing
    where
        difference :: Fun
                   -> [Expr] 
                   -> [Expr] 
                   -> Maybe (ArgumentPos, Expr, Expr)
        difference g0 xs ys = 
            differs_by_one xs ys <|> do
                unit <- isAssociative mm' g0
                (c,x,y) <- differs_by_segment 
                    (flatten_assoc g0 xs) 
                    (flatten_assoc g0 ys)
                let f = typ_fun2 $ g0 & arguments %~ take 2
                    funApp (x:xs) = L.foldl' f (Right x) $ L.map Right xs
                    funApp [] = unit
                return (c,$typeCheck$ funApp x,$typeCheck$ funApp y)
        shared :: Eq a => [a] -> [a] -> Bool
        shared xs ys = not $ L.null $ intersect xs ys
        mono :: Name -> Fun -> [Expr] -> [Expr] -> Maybe Expr
        mono rel fun xs ys = do
            (i,x,y) <- difference fun xs ys
            g       <- isMonotonic mm' rel (view name fun) i
            return ($typeCheck $ g (Right x) (Right y))
        mm' = po^.syntacticThm
        g   = po^.goal
        ctx = po^.context
        po' = po & nameless %~ (++ [znot g])

entailment :: (IsExpr expr,IsName n,TypeSystem2 t,IsQuantifier q)
           => GenSequent n t q expr 
           -> GenSequent n t q expr 
           -> (GenSequent n t q expr,GenSequent n t q expr)
entailment s0 s1 = (po0,po1)
    where
        xp0 = s0^.goal
        xp1 = s1^.goal
        ctx = (s0^.context) `merge_ctx` (s1^.context)
        po0 = empty_sequent & context .~ ctx
                            & goal    .~ xp0 `zimplies` xp1 
        po1 = s1 & context .~ ctx
                 & goal    .~ zall (s0^.nameless ++ ascElems (s0^.named))

instance (NFData n,NFData t,NFData q,NFData expr) 
    => NFData (GenSequent n t q expr)
instance NFData SyntacticProp
instance NFData Rel
instance NFData t => NFData (ArgDep t)

instance ( Ord n, Arbitrary n, Arbitrary t, Arbitrary q, Arbitrary e
         , IsQuantifier q, TypeSystem t )
        => Arbitrary (GenSequent n t q e) where
    arbitrary = scale (`div` 4) genericArbitrary
    shrink = genericShrink

instance Arbitrary SyntacticProp where
    arbitrary = scale (`div` 4) genericArbitrary
    shrink = genericShrink

instance ZoomEq Flipping where
instance ZoomEq Rel where
instance Arbitrary Rel where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance ZoomEq a => ZoomEq (ArgDep a) where
instance Arbitrary a => Arbitrary (ArgDep a) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance (Ord n,Serialize n,Serialize t,Serialize q,Serialize expr) 
    => Serialize (GenSequent n t q expr) where
instance Serialize SyntacticProp where
instance Serialize a => Serialize (ArgDep a) where
instance Serialize Rel where
