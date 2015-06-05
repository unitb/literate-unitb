{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DeriveDataTypeable     #-}
module Logic.Proof.Sequent where

    -- Modules
import Logic.Expr

    -- Libraries
import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding (Context)

import Data.Char
import Data.Default
import Data.DeriveTH
import Data.List as L
import Data.List.Ordered as OL hiding (merge)
import Data.Map    as M hiding ( map )
import Data.Maybe  as MM hiding (fromJust)
import Data.Monoid as MM
import qualified Data.Set  as S
import Data.Typeable

import GHC.Generics (Generic)

import Utilities.Format
import Utilities.Instances
import Utilities.TH

type Sequent = AbsSequent GenericType HOQuantifier

type Sequent' = AbsSequent GenericType FOQuantifier

type FOSequent = AbsSequent FOType FOQuantifier

data SyntacticProp = SyntacticProp  
        { _associative  :: Map String ExprP
        , _monotonicity :: Map (Relation,Function) (ArgDep Rel) }
            -- (rel,fun) --> rel
    deriving (Eq,Show,Generic)

preserve :: Fun -> [String] -> [((String,String),ArgDep Rel)]
preserve op funs = [((name op,f),Independent $ Rel op Direct) | f <- funs ]

type Function = String

type Relation = String

data Flipping = Flipped | Direct
    deriving (Eq,Show,Generic,Typeable)

data Rel = Rel Fun Flipping
    deriving (Eq,Show,Generic,Typeable)

data ArgDep a = Side (Maybe a) (Maybe a) | Independent a
    deriving (Eq,Generic,Show,Typeable)

data ArgumentPos = RightArg | LeftArg | MiddleArg
    deriving (Show)

data AbsSequent t q = Sequent 
        { _absSequentContext  :: AbsContext t q
        , _absSequentSyntacticThm :: SyntacticProp
        , _absSequentNameless :: [AbsExpr t q] 
        , _absSequentNamed :: Map Label (AbsExpr t q)
        , _absSequentGoal  :: AbsExpr t q }
    deriving (Eq, Generic)

-- class HasGoal a b | a -> b where
--     goal :: Getter a b

makeFields ''AbsSequent
makeLenses ''AbsSequent
makeClassy ''SyntacticProp
mkCons ''SyntacticProp

instance Default SyntacticProp where
    def = empty_monotonicity

expressions :: Getter (AbsSequent t q) [AbsExpr t q]
expressions = to $ \s -> (s^.goal) : (s^.nameless) ++ (M.elems $ s^.named)

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
isAssociative sp f = name f `M.lookup` (sp^.associative)

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

instance HasAbsContext (AbsSequent a b) a b where
    absContext = context

empty_monotonicity :: SyntacticProp
empty_monotonicity = makeSyntacticProp

instance Monoid SyntacticProp where
    mempty = genericMEmpty
    mconcat = genericMConcat
    mappend = genericMAppend

empty_sequent :: TypeSystem2 t => AbsSequent t q
empty_sequent = (Sequent empty_ctx empty_monotonicity [] M.empty ztrue)

instance (TypeSystem t, IsQuantifier q) => Show (AbsSequent t q) where
    show s =
            unlines (
                   map (" " ++)
                (  ["sort: " ++ intercalate ", " (map f $ toList ss)]
                ++ (map show $ elems fs)
                ++ (map show $ elems ds)
                ++ (map show $ elems vs)
                ++ map pretty_print' (elems hs))
                ++ ["|----"," " ++ pretty_print' g] )
        where
            Context ss vs fs ds _ = s^.context
            hs = s^.named
            g  = s^.goal
            f (_, IntSort) = ""
            f (_, BoolSort) = ""
            f (_, RealSort) = ""
            f (x, Datatype args n _) = f (x, Sort n n $ length args)
            f (x, DefSort y z xs _)  = f (x, Sort y z $ length xs)
            f (_, Sort _ z 0) = z
            f (_, Sort _ z n) = format "{0} [{1}]" z (intersperse ',' $ map chr $ take n [ord 'a' ..]) 

remove_type_vars :: Sequent' -> FOSequent
remove_type_vars (Sequent ctx m asm hyp goal) = Sequent ctx' m asm' hyp' goal'
    where
        (Context sorts _ _ dd _) = ctx
        _ = dd :: Map String Def'
        asm_types = MM.catMaybes 
                    $ map type_strip_generics 
                    $ S.elems $ S.unions 
                    $ map used_types $ map target (M.elems dd) ++ asm ++ M.elems hyp
        seq_types = S.fromList asm_types `S.union` used_types goal'
        -- seq_types = S.unions $ L.map referenced_types $ asm_types ++ S.toList (used_types goal')

        decl_types :: S.Set FOType
        decl_types = S.unions $ map used_types $ goal' : asm' ++ M.elems hyp'
        
        ctx' :: FOContext
        ctx'  = to_fol_ctx decl_types ctx
        asm' :: [FOExpr]
        asm' = map snd $ concatMap (gen_to_fol seq_types (label "")) asm
        hyp' :: Map Label FOExpr
        hyp' = M.fromList $ concat $ M.elems $ M.mapWithKey (gen_to_fol seq_types) hyp
        goal' :: FOExpr
        goal' = vars_to_sorts sorts goal

one_point :: (IsQuantifier q, TypeSystem2 t) => AbsSequent t q -> AbsSequent t q
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

flatten_assoc :: Fun -> [Expr] -> [Expr]
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
        let 
            g = po^.goal
            ctx = po^.context
            po'  = po & nameless %~ (++ [znot g])
        in
        case g of
            Binder Forall (Var nam t:vs) rs ts _ -> do
                let v   = Var (fresh nam $ symbols ctx) t
                    g'
                        | L.null vs = rs `zimplies` ts
                        | otherwise = zforall vs rs ts
                return $ apply_monotonicity $ po' & constants %~ M.insert (name v) v
                                                  & goal .~ rename nam (name v) g'
            FunApp f [lhs, rhs] ->
                case (lhs,rhs) of
                    (Binder Forall vs r0 t0 _, Binder Forall us r1 t1 _) 
                        | shared vs us && name f `elem` ["=","=>"] -> do
                            let vs0 = vs L.\\ us
                                vs1 = us L.\\ vs
                                vs' = L.intersect vs us
                            return $ apply_monotonicity $ 
                                po' & goal .~ 
                                    (zforall vs' ztrue $ 
                                        FunApp f [zforall vs0 r0 t0, zforall vs1 r1 t1])
                    (Binder Exists vs r0 t0 _, Binder Exists us r1 t1 _) 
                        | shared vs us && name f `elem` ["=","=>"] -> do
                            let vs0 = vs L.\\ us
                                vs1 = us L.\\ vs
                                vs' = L.intersect vs us
                            return $ apply_monotonicity $
                                po' & goal .~ 
                                    (zforall vs' ztrue $ 
                                        FunApp f [zexists vs0 r0 t0, zexists vs1 r1 t1])
                    (Binder q0 vs r0 t0 _, Binder q1 us r1 t1 _)
                        | q0 == q1 && vs == us 
                            && r0 == r1 && name f == "=" -> 
                                return $ apply_monotonicity $
                                    po' & goal .~ (zforall vs r0 $ t0 `zeq` t1)
                        | q0 == q1 && vs == us 
                            && t0 == t1 && name f == "=" -> 
                                return $ apply_monotonicity $
                                    po' & goal .~ (zforall vs ztrue $ r0 `zeq` r1)
                    (FunApp g0 xs, FunApp g1 ys)
                        | (length xs /= length ys && isNothing (isAssociative mm' g0))
                            || g0 /= g1 -> Nothing
                        | name f == "=" -> do
                            (_,x,y) <- difference g0 xs ys
                            return $ apply_monotonicity $
                                po' & goal .~ FunApp f [x, y]
                        | otherwise -> do
                                -- and(0,1), or(0,1), 
                                --      =>(1)       -> f.x => f.y -> x => y
                                -- not (0), =>(0)   -> f.x => f.y -> y => x
                                -- | arithmetic relations are not implement
                                -- <=(0)            -> f.x => f.y -> y <= x
                                -- <=(1)            -> f.x => f.y -> x <= y
                                -- +(0,1),-(0)      -> f.x <= f.y -> x <= y
                                -- -(1)             -> f.x <= f.y -> y <= x
                                -- | How would we treat the case of:
                                -- | context => a+b+x R a+b+y
                                -- | we need a means to distinguish an 
                                -- | implication that introduces contextual
                                -- | information
                            x <- mono (name f) g0 xs ys
                            return $ apply_monotonicity $ po' & goal .~ x
--                            let op = name g0
--                                mono i xs
--                                    | (op `elem` ["and","or"]) ||
--                                        (op == "=>" && i == 1)     = FunApp f xs
--                                    |  op == "not" ||
--                                        (op == "=>" && i == 0)     = FunApp f $ reverse xs
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
        difference g0 xs ys = 
            differs_by_one xs ys <|> do
                unit <- isAssociative mm' g0
                (c,x,y) <- differs_by_segment 
                    (flatten_assoc g0 xs) 
                    (flatten_assoc g0 ys)
                let f = typ_fun2 g0
                    funApp (x:xs) = L.foldl f (Right x) $ L.map Right xs
                    funApp [] = unit
                return (c,$fromJust$ funApp x,$fromJust$ funApp y)
        shared :: Eq a => [a] -> [a] -> Bool
        shared xs ys = not $ L.null $ intersect xs ys
        mono :: String -> Fun -> [Expr] -> [Expr] -> Maybe Expr
        mono rel fun xs ys = do
            (i,x,y) <- difference fun xs ys
            g       <- isMonotonic mm' rel (name fun) i
            return ($fromJust $ g (Right x) (Right y))
        mm' = po^.syntacticThm

fresh :: String -> Map String () -> String
fresh name xs = head $ ys `minus` M.keys xs
    where
        ys = name : map f [0..]
        f x = name ++ show x

entailment :: Sequent -> Sequent -> (Sequent,Sequent)
entailment s0 s1 = (po0,po1)
    where
        xp0 = s0^.goal
        xp1 = s1^.goal
        ctx = (s0^.context) `merge_ctx` (s1^.context)
        po0 = empty_sequent & context .~ ctx
                            & goal    .~ xp0 `zimplies` xp1 
        po1 = s1 & context .~ ctx
                 & goal    .~ zall (s0^.nameless ++ elems (s0^.named))

derive makeNFData ''AbsSequent
derive makeNFData ''SyntacticProp
derive makeNFData ''Rel
derive makeNFData ''Flipping
derive makeNFData ''ArgDep

