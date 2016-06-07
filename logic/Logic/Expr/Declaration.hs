{-# LANGUAGE LambdaCase,TypeFamilies,ScopedTypeVariables #-}
module Logic.Expr.Declaration where

    -- Module
import Logic.Expr.Classes
import Logic.Expr.Context
import Logic.Expr.Expr
import Logic.Expr.Type
import Logic.Names

    -- Library
import Control.Arrow
import Control.DeepSeq
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',List,rewriteM)
import Control.Monad.Reader
import Control.Precondition

import Data.Graph.Array
import qualified Data.Map.Class as M
import Data.Typeable

import GHC.Generics.Instances

import Text.Pretty

import Utilities.Functor

type Decl = AbsDecl GenericType HOQuantifier

type FODecl = AbsDecl FOType FOQuantifier

data AbsDecl t q = 
        FunDecl [t] InternalName [t] t
        | ConstDecl InternalName t
        | FunDef [t] InternalName [AbsVar InternalName t] t (AbsExpr InternalName t q)
        | SortDecl Sort
    deriving (Generic)

class Symbol a t q where
    decl :: Pre => a -> [AbsDecl t q]

instance IsName n => Symbol (AbsVar n t) t q where
    decl (Var name typ)        = [ConstDecl (asInternal name) typ]

instance HasName (AbsDecl t q) InternalName where
    name = to $ \case 
        (FunDecl _ n _ _)  -> n
        (ConstDecl n _)    -> n
        (FunDef _ n _ _ _) -> n
        (SortDecl s)       -> s^.name.to asInternal

instance (TypeSystem t,Typeable q) => Named (AbsDecl t q) where
    type NameOf (AbsDecl t q) = InternalName
    decorated_name' d@(FunDef ts _ _ _ _) = do
        ts' <- mapM z3_decoration' ts
        let suf = concat ts'
        onInternalName (addSuffix suf) 
            $ adaptName $ d^.name
    decorated_name' d@(FunDecl ts _ _ _)  = do
        ts' <- mapM z3_decoration' ts
        let suf = concat ts'
        onInternalName (addSuffix suf) 
            $ adaptName $ d^.name
    decorated_name' (ConstDecl n _)     = adaptName n
    decorated_name' (SortDecl s) = decorated_name' s

instance (TypeSystem t, IsQuantifier q) => Tree (AbsDecl t q) where
    as_tree' d@(FunDecl _ _ dom ran) = do
            argt <- mapM as_tree' dom
            t    <- as_tree' ran
            n    <- onOutputName render $
                    decorated_name' d
            return $ List [ Str "declare-fun", 
                Str n, 
                (List argt), t ]
    as_tree' (ConstDecl n t) = do
            t' <- as_tree' t
            return $ List [ Str "declare-const", Str $ render n, t' ]
    as_tree' d@(FunDef _ _ dom ran val) = do
            argt <- mapM as_tree' dom
            rt   <- as_tree' ran
            def  <- as_tree' val
            n    <- onOutputName render $
                    decorated_name' d
            return $ List [ Str "define-fun", 
                Str n, (List argt), 
                rt, def ]
    as_tree' (SortDecl IntSort)    = return $ Str "; comment: we don't need to declare the sort Int"
    as_tree' (SortDecl BoolSort)   = return $ Str "; comment: we don't need to declare the sort Bool" 
    as_tree' (SortDecl RealSort)   = return $ Str "; comment: we don't need to declare the sort Real"
    as_tree' (SortDecl (RecordSort m)) = as_tree' (SortDecl (Datatype args rec 
            [(make,zip fields (GENERIC . asInternal <$> args))]) :: AbsDecl t q)
        where
            args = [ makeZ3Name $ "a" ++ show i | i <- [1..M.size m] ]
            rec    = recordName m
            make   = makeZ3Name $ z3Render rec
            fields = accessorName <$> M.keys m
    as_tree' (SortDecl s@(Sort _ _ n)) = do
            return $ List [ 
                Str "declare-sort",
                Str (render $ z3_name s),
                Str $ show n ]
    as_tree' (SortDecl s@(DefSort _ _ xs def)) = do
            def' <- as_tree' def 
            return $ List 
                [ Str "define-sort"
                , Str (render $ z3_name s)
                , List $ map (Str . render) xs
                , def'
                ]
    as_tree' (SortDecl (Datatype xs n alt)) = do
            alt' <- mapM (f.(render *** map (first render))) alt
            return $ List 
                [ Str "declare-datatypes"
                , List $ map (Str . render) xs
                , List [List (Str (render n) : alt')] ]
        where
            f (x,[])    = return $ Str x
            f (x,xs)    = do
                ys <- mapM g xs
                return $ List (Str x : ys)
            g (n,t)     = do
                t' <- as_tree' t
                return $ List [Str n, t']
    rewriteM _ = pure

instance (IsQuantifier t,TypeSystem n) 
        => PrettyPrintable (AbsDecl n t) where
    pretty e = pretty $ runReader (as_tree' e) UserOutput

instance Symbol Sort t q where
    decl s = [SortDecl s]

instance IsName n => Symbol (AbsFun n t) t q where
    decl (Fun xs name Unlifted params ret _) = [FunDecl xs (asInternal name) params ret]
    decl _ = error "Symbol.decl: cannot declare lifted functions"

instance IsName n => Symbol (AbsDef n t q) t q where
    decl (Def xs name ps typ ex)  = [
            FunDef xs (asInternal name) (map translate ps) typ $ fmap3 asInternal ex]

instance (IsName n,Ord t,IsQuantifier q,TypeSystem t) 
        => Symbol (GenContext n t q) t q where
    decl (Context sorts cons fun defs _) = -- dums) = 
                concatMap decl (M.ascElems sorts)
--            ++  concatMap decl (elems (cons `merge` dums)) 
            ++  concatMap decl (M.ascElems cons) 
            ++  concatMap decl (M.ascElems fun) 
            ++  concatMap decl (sortDefs defs)

sortDefs :: ( IsName n,Ord t,Ord q
            , IsQuantifier q 
            , TypeSystem t )
         => M.Map n (AbsDef n t q) 
         -> [AbsDef n t q]
sortDefs defs = M.ascElems defA
                    ++ (acyclic <$> top_sort (M.ascElems defB) es)
                            
        where
            edges d v = d `M.intersection` used_var' (v^.defExpr)
            (defA,defB) = M.partition (M.null . edges defs) defs
            es = [ (v,v') | v  <- M.elems defB
                          , v' <- M.elems $ edges defB v ]

mk_context :: TypeSystem t => [AbsDecl t q] -> GenContext InternalName t q
mk_context (x:xs) = 
        case mk_context xs of
            Context ss vs fs defs dums -> 
                case x of
                    SortDecl s ->
                        Context
                            (M.insert (s^.name) s ss) vs
                            fs defs dums
                    ConstDecl n t -> 
                        Context 
                            ss (M.insert n (Var n t) vs) 
                            fs defs dums
                    FunDecl gs n ps t -> 
                        Context 
                            ss vs 
                            (M.insert n (Fun gs n Unlifted ps t InfiniteWD) fs)
                            defs dums
                    FunDef gs n ps t e -> 
                        Context 
                            ss vs fs 
                            (M.insert n (Def gs n ps t e) defs) 
                            dums
mk_context [] = empty_ctx

instance (NFData t,NFData q) => NFData (AbsDecl t q)
