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
{-# LANGUAGE GADTs  #-}
module Logic.Theory 
    ( Theory(..)
    , fact
    , mzforall'
    , mzexists'
    , make_theory
    , command
    , function
    , dummy
    , operator
    , Logic.Theory.sort
    , sort_def
    , type_param
    , assert
    , axiom, axioms
    , th_notation
    , theory_ctx
    , theory_facts
    , empty_theory
    , basic_theory )
where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Proof (Proof)

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.DeepSeq
import Control.Monad.RWS
import Control.Monad.Writer
import Control.Lens hiding (Context,(.=),from,to)

import           Data.DeriveTH
import           Data.Either
import           Data.Either.Combinators
import           Data.List as L
import           Data.Map as M hiding ( map )
import qualified Data.Set as S
import           Data.Typeable

import GHC.Generics hiding ((:+:))

import Language.Haskell.TH hiding (Type)

import Utilities.Format
import Utilities.TH
import Utilities.Tuple hiding (len)

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
        , dummies    :: Map String Var 
        , theorems   :: Map Label (Maybe Proof)
        , thm_depend :: [ (Label,Label) ]
        , notation   :: Notation }
    deriving (Eq, Show, Typeable, Generic)

makeLenses ''Theory
mkCons ''Theory

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
           , (label "@basic@@_1", axm1)]
        , notation = functions }
   where
--        t  = VARIABLE "t"
        t0 = VARIABLE "t0"
        t1 = VARIABLE "t1"
        (x,x_decl) = var "x" t0
        (y,y_decl) = var "y" t1
--        axm0 = fromJust $ mzforall [x_decl,y_decl] mztrue $
--                mzeq x y `mzeq` mzeq_symb x y
        axm0 = $fromJust $ mzforall [x_decl,y_decl] mztrue $ 
            zselect (zconst x) y .= x
        axm1 = $fromJust $ mzforall [x_decl] mztrue $
            zselect zident x .= x

empty_theory :: Theory
empty_theory = makeTheory
    { notation = with_assoc empty_notation }

th_notation :: Theory -> Notation
th_notation th = res
    where
        ths = th : elems (extends th)
        res = flip precede logic
            $ L.foldl combine empty_notation 
            $ map notation ths

theory_ctx :: Theory -> Context
theory_ctx th = 
        merge_all_ctx $
            (Context ts c new_fun (defs th) dums) : L.map theory_ctx (M.elems d)
    where
        d      = extends th
        ts     = types th
        fun    = funs th
        c      = consts th
        dums   = dummies th
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
declAxiom loc stmt = tell [mapLeft (map (locMsg loc ++)) $ zcast bool $ withForall stmt]

withForall :: ExprP -> ExprP 
withForall mx = do
    x <- mx
    let vs = S.toList $ used_var x
    mzforall vs mztrue $ Right x

axiom :: ExpQ
axiom = withLoc 'declAxiom

axioms :: String -> Writer [ExprP] () -> Map Label Expr
axioms name cmd
        | L.null ls = fromList $ L.map (first $ label . format "@{0}@@_{1}" name) $ zip ns rs
        | otherwise = error $ unlines $ concat ls
    where
        n  = length rs
        ns = map (pad . show) [1..n]
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
    gBuild _ xs = K1 $ with_assoc 
        $ L.foldl combine empty_notation 
        $ map unK1 xs        

instance GBuild (K1 i a) where
    gBuild (K1 m) _ = K1 m

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
    len :: Proxy s -> Int

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
    len Proxy = 0
    funDecl' name tp (args,rt) = mk_fun (reverse tp) name (typeList $ toTuple args) rt
    utility' fun Proxy = utilityImpl fun [] (Proxy :: Proxy (TypeList t))

instance Signature t => Signature (Type -> t) where
    type FunType (Type -> t) = FunType t
    len Proxy = 1 + len (Proxy :: Proxy t)
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
        x = either (error . unlines . map (locMsg loc ++)) id 
            $ zcast bool $ withForall stmt

assert :: ExpQ
assert = withLoc 'assert'

dummy :: VarSignature s => String -> s -> M ExprP
dummy n s = M $ do
    let v = varDecl n s
    tell [ empty_theory { dummies = singleton n v } ]
    return $ Right $ Word v

command :: forall s. (FromList (FunType s) ExprP, Signature s)
        => String -> s -> M (FunType s)
command n s = do
    f <- function n s
    let proxy = Proxy :: Proxy s
        cmd = Command ('\\':n) n (len proxy) (from_list f)
    M $ tell [ empty_theory
        { notation = empty_notation { commands = [cmd] } } ]
    return f

function :: Signature s => String -> s -> M (FunType s)
function n s = M $ do
    tell [empty_theory 
        { funs = singleton n (funDecl n s) } ]
    return $ utility n s

operator :: (Signature s, FunType s ~ (ExprP -> ExprP -> ExprP))
         => String -> String -> s -> M (ExprP -> ExprP -> ExprP)
operator op tag s = do
    f <- function tag s
    let binop = BinOperator tag op f
    M $ tell [empty_theory 
            { notation = empty_notation { new_ops = [Right binop] } } ]
    return f

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

newtype M a = M { runM :: RWS () [Theory] Int a }

instance Applicative M where
    pure  = return
    (<*>) = ap

instance Functor M where
    fmap = liftM

instance Monad M where
    x >>= f = M $ runM x >>= (runM . f)
    return = M . return

clash :: (Show a, Ord a)
      => (thy -> Map a b) -> [thy] -> Map a b
clash f xs 
        | L.null es = M.unions $ L.map f xs
        | otherwise = error $ format "Name clash with: {0}" $ intercalate "," (map show es)
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
