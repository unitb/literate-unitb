{-# LANGUAGE KindSignatures
    , TypeFamilies
    , TypeOperators
    , ScopedTypeVariables
    , UndecidableInstances #-}
module Logic.Theory.Monad where

    -- Modules
import Logic.Expr
import Logic.Expr.Genericity (variables)
import Logic.Operator
import Logic.Proof hiding (preserve) 
import qualified Logic.Proof as P

import Logic.Theory.Internals

    -- Libraries
import Control.Arrow
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import Control.Lens hiding (Context,from,to,rewriteM)
import Control.Precondition

import           Data.Either
import           Data.Either.Combinators
import           Data.List as L
import           Data.Map.Class as M
import qualified Data.Set as S
import           Data.Typeable

import Language.Haskell.TH hiding (Type,Name)

import Text.Printf.TH

import Utilities.Error
import Utilities.Table
import Utilities.Tuple

class Signature s where
    type FunType s :: *
    funDecl' :: Name -> [Type] -> s -> Fun
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
        let ts' = repeat $ VARIABLE $ fromString'' "unexpected"
            (Fun _ n _ ts t _) = fun
            f e t = unlines
                    [ [printf|    argument: %s|] (pretty e)
                    , [printf|      type: %s|] (pretty $ type_of e)
                    , [printf|      expected type: %s|] (pretty t) ] 
            err_msg = unlines $
                    [ [printf|arguments of '%s' do not match its signature:|] (render n)
                    , [printf|   signature: %s -> %s|] (pretty ts) (pretty t)
                    ] ++ zipWith f args (ts ++ ts')
        maybe (Left [err_msg]) Right 
            $ check_args args fun

utility :: forall s. (Signature s) 
        => Name -> s -> FunType s
utility name f = utility' (funDecl name f) (Proxy :: Proxy s)

instance SignatureImpl as => SignatureImpl (Type :+: as) where
    type FunTypeImpl (Type :+: as) = ExprP -> FunTypeImpl as
    typeList (t :+: ts) = t : typeList ts
    utilityImpl fun args Proxy e = utilityImpl fun (e:args) (Proxy :: Proxy as)

funDecl :: (Signature s) => Name -> s -> Fun
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
            p = fromString'' [toEnum $ fromEnum 'a' + length tp]
            gP = GENERIC p
    utility' fun Proxy = utility' fun (Proxy :: Proxy t)

class VarSignature s where
    varDecl' :: Int -> Name -> s -> Var

varDecl :: (VarSignature s) 
        => Name -> s -> Var
varDecl = varDecl' 0

instance VarSignature Type where
    varDecl' _ = Var

instance VarSignature t => VarSignature (Type -> t) where
    varDecl' n name t = varDecl' (n+1) name (t gP)
        where
            p  = fromString'' [toEnum $ fromEnum 'a' + n]
            gP = GENERIC p

class TypeSignature s where
    mkSort' :: Sort -> [Type] -> s
    order :: Proxy s -> Int

mkSort :: forall s. (TypeSignature s) => Name -> (s,Sort)
mkSort n = (mkSort' s [],s)
    where
        s = Sort n (asInternal n) $ order (Proxy :: Proxy s)

instance TypeSignature Type where
    mkSort' s ts = make_type s $ reverse ts
    order Proxy  = 0

class TypeDefSignature t where
    mkSortDef' :: Name -> [Name] -> t -> ([Type] -> t,Sort)

mkSortDef :: (TypeDefSignature t) 
          => Name -> t -> (t,Sort)
mkSortDef n f = first ($ []) $ mkSortDef' n [] f

instance TypeDefSignature Type where
    mkSortDef' n ps t = (\ts -> make_type s $ reverse ts,s)
        where
            s = DefSort n 
                (asInternal n) 
                (reverse ps) t

instance TypeDefSignature t => TypeDefSignature (Type -> t) where
    mkSortDef' n ps f = (\ts t -> f' $ t:ts,s)
        where
            (f',s) = mkSortDef' n (p:ps) (f t)
            p :: IsName n => n
            p = fromString'' [toEnum $ fromEnum 'a' + length ps]
            t = GENERIC p

instance TypeSignature s => TypeSignature (Type -> s) where
    mkSort' s ts t = mkSort' s (t:ts)
    order Proxy = 1 + order (Proxy :: Proxy s)

assert' :: Loc -> ExprP -> M ()
assert' loc stmt = do
    M $ tell [x]
    where
        x = either (error . unlines . L.map (locMsg loc ++)) id 
            $ zcast bool $ withForall stmt

assert :: ExpQ
assert = withLoc 'assert'

dummy :: (VarSignature s) => String -> s -> M ExprP
dummy n s = do
    let v = varDecl name s
        name = fromString'' n
    tellTheory $ dummies <>= singleton name v
    return $ Right $ Word v

command :: forall s. (FromList (FunType s) ExprP, Signature s)
        => Name -> s -> M (FunType s)
command n s = do
    let name = addBackslash n
    (mk,f) <- function (asInternal n) s
    let proxy = Proxy :: Proxy s
        cmd = Command 
                name 
                (asInternal n)
                (len' proxy) f
    tellTheory $ notation.commands <>= [cmd]
    return mk

function :: (Signature s) => InternalName -> s -> M (FunType s,Fun)
function n s = do
    let n' = asName n
        fun = funDecl n' s
    tellTheory $ funs <>= singleton n' fun
    return (utility n' s,fun)

operator :: (Signature s, FunType s ~ (ExprP -> ExprP -> ExprP))
         => Name -> InternalName 
         -> s -> M (Operator,ExprP -> ExprP -> ExprP)
operator op tag s = do
    (mk,f) <- function tag s
    let binop = BinOperator tag op Direct f
    tellTheory $ notation.new_ops <>= [Right binop]
    return (Right binop,mk)

unary :: (Signature s, FunType s ~ (ExprP -> ExprP))
      => Name -> InternalName -> s -> M (Operator,ExprP -> ExprP)
unary op tag s = do
    (mk,f) <- function tag s
    let unop = UnaryOperator tag op f
    tellTheory $ notation.new_ops %= (Left unop:)
    return (Left unop,mk)

preserve :: Fun -> [Function] -> M ()
preserve rel fun = tellTheory $
    syntacticThm.monotonicity <>= M.fromList (P.preserve rel fun)

associativity :: Function -> ExprP -> M ()
associativity fun e = tellTheory $ do
        syntacticThm.associative <>= M.singleton fun e

left_associativity :: [Operator] -> M ()
left_associativity ops = tellTheory $ do
        notation.left_assoc <>= [L.map (fromRight $ $myError "") ops]

right_associativity :: [Operator] -> M ()
right_associativity ops = tellTheory $ do
        notation.right_assoc <>= [L.map (fromRight $ $myError "") ops]

precedence :: [Operator] 
           -> [[Operator]]
           -> [Operator]
           -> M ()
precedence vs ops us = tellTheory $
        notation.prec <>= [vs : ops ++ [us]]

uniqueId :: M Int
uniqueId = M $ do
    n <- use _1
    _1 .= n + 1
    return n

type_param :: M Type
type_param = do
    n <- uniqueId
    return $ VARIABLE $ fromString'' $ "t" ++ show n

sort :: TypeSignature s => Name -> M s
sort n = do
    let (r,s) = mkSort n
    tellTheory $ types .= singleton n s
    return r

sort_def :: TypeDefSignature s => Name -> s -> M s
sort_def n f = do
    let (r,s) = mkSortDef n f
    tellTheory $ types <>= singleton n s
    return r    

param_to_var :: Expr -> Expr
param_to_var e = evalState (param_to_varE e) (0,variables e,M.empty)

type RewriteST = State (Int,S.Set InternalName,Map InternalName InternalName)

param_to_varE :: Expr -> RewriteST Expr
param_to_varE e = do
    e' <- rewriteM param_to_varE e
    case e' of
        FunApp (Fun ps n lift args rt wd) xs -> do
            FunApp <$> (Fun <$> mapM param_to_varT ps 
                            <*> pure n 
                            <*> pure lift 
                            <*> mapM param_to_varT args 
                            <*> param_to_varT rt
                            <*> pure wd) 
                   <*> pure xs
        _ -> return e'

param_to_varT :: Type -> RewriteST Type
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
            if (fromString'' $ "t" ++ show i) `S.member` vs 
                then next_free
                else return $ fromString'' $ "t" ++ show i
param_to_varT t = rewriteM param_to_varT t

newtype M a = M (RWS () [Expr] (Int,Theory) a)
    deriving (Applicative,Functor,Monad)

clash :: (PrettyPrintable a, Ord a)
      => (thy -> Map a b) -> [thy] -> Map a b
clash f xs 
        | L.null es = M.unions $ L.map f xs
        | otherwise = error $ [printf|Name clash with: %s|] $ intercalate "," (L.map pretty es)
    where
        es = keys $ M.unions $ do
            (x,ys) <- zip xs $ drop 1 $ tails xs
            y      <- ys
            return $ M.intersection (f x) (f y)

make_theory' :: Pre 
             => String -> State Theory () -> Theory
make_theory' name cmd = make_theory name $ M $ zoom _2 (state $ runState cmd)

make_theory :: Pre 
            => String -> M () -> Theory
make_theory name (M cmd) = t'
    where
        name' = fromString'' name
        ((_,t),es) = execRWS cmd () (0,empty_theory name')
        es' = zipWith (\i -> (pad i,)) [0..] es
        t' = t & fact %~ M.union (fromList es')
        n = length $ show $ length es
        pad m = label $ name ++ replicate (n - length (show m)) ' ' ++ show m

tellTheory :: State Theory () -> M ()
tellTheory cmd = M $ zoom _2 (state $ runState cmd)
        --n <- ask
        --tell [execState cmd $ empty_theory n]

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

declAxiom :: Loc -> ExprP -> Writer [ExprP] ()
declAxiom loc stmt = tell [mapLeft (L.map (locMsg loc ++)) $ zcast bool $ withForall stmt]

withForall :: ExprP -> ExprP 
withForall mx = do
    x <- mx
    let vs = S.toList $ used_var x
    param_to_var <$> mzforall vs mztrue (Right x)

axiom :: ExpQ
axiom = withLoc 'declAxiom

axioms :: String -> Writer [ExprP] () -> Table Label Expr
axioms name cmd
        | L.null ls = fromList $ L.map (first $ label . [printf|@%s@@_%s|] name) $ zip ns rs
        | otherwise = error $ unlines $ concat ls
    where
        n  = length rs
        ns = L.map (pad . show) [1..n]
        pad ys = replicate (n - length ys) ' ' ++ ys
        rs = rights xs
        ls = lefts xs
        xs = execWriter cmd
