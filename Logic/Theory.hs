{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving  #-}
{-# LANGUAGE GADTs  #-}
module Logic.Theory 
    ( Theory(..)
    , fact
    , mzforall'
    , mzexists'
    , make_theory
    , all_theories
    , syntacticThm
    , command
    , function
    , dummy
    , operator
    , unary
    , Logic.Theory.sort
    , sort_def
    , type_param
    , assert
    , precedence
    , left_associativity
    , right_associativity
    , preserve
    , associativity
    , axiom, axioms
    , th_notation
    , theory_ctx
    , theory_facts
    , empty_theory
    , basic_theory )
where

    -- Modules
import Logic.Expr
import Logic.Expr.Genericity (variables)
import Logic.Operator
import Logic.Proof hiding (preserve) 
import qualified Logic.Proof as P

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.DeepSeq
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Control.Lens hiding (Context,(.=),from,to,rewriteM)

import           Data.DeriveTH
import           Data.Either
import           Data.Either.Combinators
import           Data.List as L
import           Data.Map as M 
import qualified Data.Set as S
import           Data.Typeable

import GHC.Generics hiding ((:+:),prec)

import Language.Haskell.TH hiding (Type)

import Utilities.Error
import Utilities.Format
import Utilities.TH
import Utilities.Tuple

    -- Obsolete doc:
    -- the use of gen_param is tricky. Be careful
    -- generic functions should have type variables in them
    -- to match those type variables, we use the generic 
    -- parameter that features corresponding /generic/
    -- types. We unify the generic parameter with all 
    -- the types of all the variables and functions
    -- and use the resulting mapping to instantiate 
    -- the type variables. The generic type (rather than
    -- the type variable) is also used in function types.
data Theory = Theory 
        { extends    :: Map String Theory
        , types      :: Map String Sort
        , funs       :: Map String Fun
        , defs       :: Map String Def
        , consts     :: Map String Var
        , _fact      :: Map Label Expr
        , _theoryDummies :: Map String Var 
        , _theorySyntacticThm :: SyntacticProp
        , theorems   :: Map Label (Maybe Proof)
        , thm_depend :: [ (Label,Label) ]
        , notation   :: Notation }
    deriving (Eq, Show, Typeable, Generic)

makeLenses ''Theory
makeFields ''Theory
mkCons ''Theory

all_theories :: Theory -> [Theory]
all_theories th = th : M.elems (all_theories' th)
    where
        _ = set theorySyntacticThm

all_theories' :: Theory -> Map String Theory
all_theories' th = M.unions $ extends th : M.elems (M.map all_theories' $ extends th)

basic_theory :: Theory
basic_theory = empty_theory 
        { types = symbol_table [BoolSort, pair_sort, set_sort]
--        , funs = symbol_table [everywhere_fun]
--        , gen_param = Just gT
--        , funs  = symbol_table [Fun [gT] "eq" [gT,gT] bool]
--        , fact  = fromList 
--            [ (label "@basic@@_0", axm0) ]
        , funs  = symbol_table [const_fun,ident_fun]
        , _fact  = fromList 
           [ (label "@basic@@_0", axm0) 
           , (label "@basic@@_1", axm1) ]
        , _theorySyntacticThm = empty_monotonicity
            { _associative = fromList 
                    [("and",mztrue)
                    ,("or", mzfalse)
                    ,("=",  mztrue)]
            , _monotonicity = fromList $
                P.preserve implies_fun ["and","or"] 
             ++ [ (("=>","not"),Independent zfollows')
                , (("=>","=>"), Side (Just zfollows')
                                     (Just zimplies')) ] }
        , notation = functional_notation }
   where
        zimplies' = Rel implies_fun Direct
        zfollows' = Rel implies_fun Flipped
        _ = theoryDummies Identity
--        t  = VARIABLE "t"
        t0 = VARIABLE "t0"
        t1 = VARIABLE "t1"
        (x,x_decl) = var "x" t0
        (y,y_decl) = var "y" t1
--        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue $
--                mzeq x y `mzeq` mzeq_symb x y
        axm0 = $typeCheck $ mzforall [x_decl,y_decl] mztrue $ 
            zselect (zconst x) y .= x
        axm1 = $typeCheck $ mzforall [x_decl] mztrue $
            zselect zident x .= x

empty_theory :: Theory
empty_theory = makeTheory
    { notation = empty_notation }

th_notation :: Theory -> Notation
th_notation th = res
    where
        ths = th : elems (extends th)
        res = flip precede logical_notation
            $ L.foldl combine empty_notation 
            $ L.map notation ths

theory_ctx :: Theory -> Context
theory_ctx th = 
        merge_all_ctx $
            (Context ts c new_fun (defs th) dums) : L.map theory_ctx (M.elems d)
    where
        d      = extends th
        ts     = types th
        fun    = funs th
        c      = consts th
        dums   = th^.dummies
        new_fun = fun

    -- todo: prefix name of theorems of a z3_decoration
theory_facts :: Theory -> Map Label Expr
theory_facts th = 
        merge_all (new_fact : L.map theory_facts (M.elems d))
    where
        d      = extends th
        facts  = _fact th
        new_fact = facts

declAxiom :: Loc -> ExprP -> Writer [ExprP] ()
declAxiom loc stmt = tell [mapLeft (L.map (locMsg loc ++)) $ zcast bool $ withForall stmt]

withForall :: ExprP -> ExprP 
withForall mx = do
    x <- mx
    let vs = S.toList $ used_var x
    param_to_var <$> mzforall vs mztrue (Right x)

axiom :: ExpQ
axiom = withLoc 'declAxiom

axioms :: String -> Writer [ExprP] () -> Map Label Expr
axioms name cmd
        | L.null ls = fromList $ L.map (first $ label . format "@{0}@@_{1}" name) $ zip ns rs
        | otherwise = error $ unlines $ concat ls
    where
        n  = length rs
        ns = L.map (pad . show) [1..n]
        pad ys = replicate (n - length ys) ' ' ++ ys
        rs = rights xs
        ls = lefts xs
        xs = execWriter cmd

class GBuild (g :: * -> *) where
    gBuild :: g p -> [g p] -> g p

instance GBuild U1 where
    gBuild _ _ = U1

instance (Show k, Ord k, Typeable a) 
        => GBuild (K1 i (Map k a)) where
    gBuild _ xs = K1 $ clash unK1 xs

instance GBuild (K1 i Notation) where
    gBuild _ xs = K1 
        $ L.foldl combine empty_notation 
        $ L.map unK1 xs        

instance GBuild (K1 i SyntacticProp) where
    gBuild _ ms = K1 $ mconcat $ L.map unK1 ms

instance GBuild (K1 i [a]) where
    gBuild _ ms = K1 $ concatMap unK1 ms

instance GBuild a => GBuild (M1 i c a) where
    gBuild (M1 m) xs = M1 $ gBuild m $ L.map unM1 xs

instance (GBuild a, GBuild b) => GBuild (a :*: b) where
    gBuild (x :*: y) xs = gBuild x (L.map fst xs) :*: gBuild y (L.map snd xs)
        where
            fst (x :*: _) = x
            snd (_ :*: x) = x

make_theory :: String -> M () -> Theory
make_theory name (M cmd) = to $ gBuild (from empty_theory) $ L.map from ts'
    where
        ts  = snd $ execRWS cmd () 0
        ts' = zipWith (\i -> fact %~ M.mapKeys (pad' i)) [0..] ts
        n = length $ show $ length ts
        pad m = name ++ replicate (n - length (show m)) ' ' ++ show m
        pad' k _ = label $ pad k

class Signature s where
    type FunType s :: *
    funDecl' :: String -> [Type] -> s -> Fun
    utility' :: Fun -> Proxy s -> FunType s
    len' :: Proxy s -> Int

class SignatureImpl ts where
    type FunTypeImpl ts :: *
    typeList :: ts -> [Type]
    utilityImpl :: Fun -> [ExprP] -> Proxy ts -> FunTypeImpl ts

instance SignatureImpl () where
    type FunTypeImpl () = ExprP
    typeList () = []
    utilityImpl fun argsM' Proxy = do
        let argsM = reverse argsM'
            es = lefts argsM
        unless (L.null es) $ Left $ concat es
        args <- sequence argsM
        let ts' = repeat $ VARIABLE "unexpected"
            (Fun _ n _ ts t) = fun
            f e t = format (unlines
                    [ "    argument: {0}" 
                    , "      type: {1}"
                    , "      expected type: {2}"])
                    e (type_of e) t :: String
            err_msg = format (unlines $
                    [  "arguments of '{0}' do not match its signature:"
                    ,  "   signature: {1} -> {2}"
                    ] ++ zipWith f args (ts ++ ts')
                    ) n ts t :: String
        maybe (Left [err_msg]) Right 
            $ check_args args fun
        -- Right (FunApp fun $ reverse args)

utility :: forall s. Signature s => String -> s -> FunType s
utility name f = utility' (funDecl name f) (Proxy :: Proxy s)

instance SignatureImpl as => SignatureImpl (Type :+: as) where
    type FunTypeImpl (Type :+: as) = ExprP -> FunTypeImpl as
    typeList (t :+: ts) = t : typeList ts
    utilityImpl fun args Proxy e = utilityImpl fun (e:args) (Proxy :: Proxy as)

funDecl :: Signature s => String -> s -> Fun
funDecl name = funDecl' name []

instance (IsTuple t, SignatureImpl (TypeList t)) => Signature (t,Type) where
    type FunType (t,Type) = FunTypeImpl (TypeList t)
    len' Proxy = tLength (Proxy :: Proxy t)
    funDecl' name tp (args,rt) = mk_fun (reverse tp) name (typeList $ toTuple args) rt
    utility' fun Proxy = utilityImpl fun [] (Proxy :: Proxy (TypeList t))

instance Signature t => Signature (Type -> t) where
    type FunType (Type -> t) = FunType t
    len' Proxy = len' (Proxy :: Proxy t)
    funDecl' name tp f = funDecl' name (gP:tp) (f gP)
        where
            p = [toEnum $ fromEnum 'a' + length tp]
            gP = GENERIC p
    utility' fun Proxy = utility' fun (Proxy :: Proxy t)

class VarSignature s where
    varDecl' :: Int -> String -> s -> Var

varDecl :: VarSignature s => String -> s -> Var
varDecl = varDecl' 0

instance VarSignature Type where
    varDecl' _ = Var

instance VarSignature t => VarSignature (Type -> t) where
    varDecl' n name t = varDecl' (n+1) name (t gP)
        where
            p  = [toEnum $ fromEnum 'a' + n]
            gP = GENERIC p

class TypeSignature s where
    mkSort' :: Sort -> [Type] -> s
    order :: Proxy s -> Int

mkSort :: forall s. TypeSignature s => String -> (s,Sort)
mkSort n = (mkSort' s [],s)
    where
        s = Sort n n $ order (Proxy :: Proxy s)

instance TypeSignature Type where
    mkSort' s ts = make_type s $ reverse ts
    order Proxy  = 0

class TypeDefSignature t where
    mkSortDef' :: String -> [String] -> t -> ([Type] -> t,Sort)

mkSortDef :: TypeDefSignature t => String -> t -> (t,Sort)
mkSortDef n f = first ($ []) $ mkSortDef' n [] f

instance TypeDefSignature Type where
    mkSortDef' n ps t = (\ts -> make_type s $ reverse ts,s)
        where
            s = DefSort n n (reverse ps) t

instance TypeDefSignature t => TypeDefSignature (Type -> t) where
    mkSortDef' n ps f = (\ts t -> f' $ t:ts,s)
        where
            (f',s) = mkSortDef' n (p:ps) (f t)
            p = [toEnum $ fromEnum 'a' + length ps]
            t = GENERIC p

instance TypeSignature s => TypeSignature (Type -> s) where
    mkSort' s ts t = mkSort' s (t:ts)
    order Proxy = 1 + order (Proxy :: Proxy s)

assert' :: Loc -> ExprP -> M ()
assert' loc stmt = M $ tell 
        [ empty_theory 
            { _fact = singleton (label "") x }]
    where
        x = either (error . unlines . L.map (locMsg loc ++)) id 
            $ zcast bool $ withForall stmt

assert :: ExpQ
assert = withLoc 'assert'

dummy :: VarSignature s => String -> s -> M ExprP
dummy n s = M $ do
    let v = varDecl n s
    tell [ empty_theory & dummies .~ singleton n v ]
    return $ Right $ Word v

command :: forall s. (FromList (FunType s) ExprP, Signature s)
        => String -> s -> M (FunType s)
command n s = do
    f <- function n s
    let proxy = Proxy :: Proxy s
        cmd = Command ('\\':n) n (len' proxy) (from_list f)
    M $ tell [ empty_theory
        { notation = empty_notation & commands .~ [cmd] } ]
    return f

function :: Signature s => String -> s -> M (FunType s)
function n s = M $ do
    tell [empty_theory 
        { funs = singleton n (funDecl n s) } ]
    return $ utility n s

operator :: (Signature s, FunType s ~ (ExprP -> ExprP -> ExprP))
         => String -> String -> s -> M (Operator,ExprP -> ExprP -> ExprP)
operator op tag s = do
    f <- function tag s
    let binop = BinOperator tag op f
    M $ tell [empty_theory 
            { notation = empty_notation & new_ops .~ [Right binop] } ]
    return (Right binop,f)

unary :: (Signature s, FunType s ~ (ExprP -> ExprP))
      => String -> String -> s -> M (Operator,ExprP -> ExprP)
unary op tag s = do
    f <- function tag s
    let unop = UnaryOperator tag op f
    M $ tell [empty_theory 
            { notation = empty_notation & new_ops .~ [Left unop] } ]
    return (Left unop,f)

preserve :: Fun -> [String] -> M ()
preserve rel fun = M $ tell [empty_theory
    & syntacticThm.monotonicity .~ M.fromList (P.preserve rel fun) ]

associativity :: String -> ExprP -> M ()
associativity fun e = M $ tell [empty_theory
    & syntacticThm.associative .~ M.singleton fun e] 

left_associativity :: [Operator] -> M ()
left_associativity ops = M $ tell [empty_theory
    { notation = empty_notation & left_assoc .~ [L.map (fromRight $ $myError "") ops] }]

right_associativity :: [Operator] -> M ()
right_associativity ops = M $ tell [empty_theory
    { notation = empty_notation & right_assoc .~ [L.map (fromRight $ $myError "") ops] }]

precedence :: [Operator] 
           -> [[Operator]]
           -> [Operator]
           -> M ()
precedence vs ops us = M $ tell [empty_theory 
    { notation = empty_notation & prec .~ [vs : ops ++ [us]] }]

type_param :: M Type
type_param = M $ do
    n <- get
    put (n+1)
    return $ VARIABLE $ "t" ++ show n

sort :: TypeSignature s => String -> M s
sort n = M $ do
    let (r,s) = mkSort n
    tell [empty_theory { types = singleton n s } ]
    return r

sort_def :: TypeDefSignature s => String -> s -> M s
sort_def n f = M $ do
    let (r,s) = mkSortDef n f
    tell [empty_theory { types = singleton n s } ]
    return r    

param_to_var :: Expr -> Expr
param_to_var e = evalState (param_to_varE e) (0,variables e,M.empty)

param_to_varE :: Expr -> State (Int,S.Set String,Map String String) Expr
param_to_varE e = do
    e' <- rewriteM param_to_varE e
    case e' of
        FunApp (Fun ps n lift args rt) xs -> do
            FunApp <$> (Fun <$> mapM param_to_varT ps 
                            <*> pure n 
                            <*> pure lift 
                            <*> mapM param_to_varT args 
                            <*> param_to_varT rt) 
                   <*> pure xs
        _ -> return e'

param_to_varT :: Type -> State (Int,S.Set String,Map String String) Type
param_to_varT t@(VARIABLE _) = return t
param_to_varT (GENERIC n) = do
        ns <- use trans
        case M.lookup n ns of
            Just n' -> return $ VARIABLE n'
            Nothing -> do
                n' <- next_free
                _3 %= M.insert n n'
                return $ VARIABLE n'
    where
        count = _1
        vars  = _2
        trans = _3
        next_free = do
            i <- use count
            _1 += 1 -- count
            vs <- use vars 
            if ("t" ++ show i) `S.member` vs 
                then next_free
                else return $ "t" ++ show i
param_to_varT t = rewriteM param_to_varT t

newtype M a = M (RWS () [Theory] Int a)
    deriving (Applicative,Functor,Monad)

clash :: (Show a, Ord a)
      => (thy -> Map a b) -> [thy] -> Map a b
clash f xs 
        | L.null es = M.unions $ L.map f xs
        | otherwise = error $ format "Name clash with: {0}" $ intercalate "," (L.map show es)
    where
        es = keys $ M.unions $ do
            (x,ys) <- zip xs $ drop 1 $ tails xs
            y      <- ys
            return $ M.intersection (f x) (f y)

mzforall' :: [ExprP] -> ExprP -> ExprP -> ExprP
mzforall' vs r t = do
    vs' <- sequence vs >>= mapM (\e -> do
        case e of
            Word v -> return v
            _ -> Left ["Cannot quantify over expressions"])
    mzforall vs' r t

mzexists' :: [ExprP] -> ExprP -> ExprP -> ExprP
mzexists' vs r t = do
    vs' <- sequence vs >>= mapM (\e -> do
        case e of
            Word v -> return v
            _ -> Left ["Cannot quantify over expressions"])
    mzexists vs' r t

derive makeNFData ''Theory
