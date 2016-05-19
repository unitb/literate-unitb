module Test.QuickCheck.AxiomaticClass where

import Control.Lens
import Control.Monad

import Data.List
import qualified Data.Map as M
import Data.Maybe

import Prelude hiding (Monoid(..))

import Language.Haskell.TH
import Language.Haskell.TH.Lens
import Language.Haskell.TH.Syntax

import Test.QuickCheck
import Test.QuickCheck.Report

import Text.Printf.TH

    -- Copied from Test.QuickCheck.All

substVars' :: (Name -> Maybe Type) -> Pred -> Pred
substVars' f = types %~ substVars f

substVars :: (Name -> Maybe Type) -> Type -> Type
substVars f t@(VarT n)          = fromMaybe t (f n)
substVars f (ForallT bs ctx ty) = ForallT bs (map (substVars' f) ctx) (substVars f ty)
substVars f (SigT t k)          = SigT (substVars f t) k
substVars f (AppT l r)          = AppT (substVars f l) (substVars f r)
substVars _ t                   = t

withInt :: Type -> Type
withInt = substVars $ const $ Just $ ConT ''Integer

quickCheckClasses :: [Name] -> ExpQ
quickCheckClasses cls = [e| $(quickCheckClassesWith cls) quickCheckResult |]

quickCheckClassesWith :: [Name] -> ExpQ
quickCheckClassesWith cls = do
    props <- concat <$> mapM quickCheckClassTests cls
    [e| (\check -> runQuickCheckAll' $(listE props) check) |]

quickCheckClassTests :: Name -> Q [ExpQ]
quickCheckClassTests cl = do
    ClassI (ClassD _ _ args _ ms) is <- reify cl
    loc <- location
    let axioms = filter (maybe False (isPrefixOf "axiom_") . nameOf) ms
        nameOf (SigD n _) = Just $ nameBase n
        nameOf _ = Nothing
        _ = args
        _ = insts

        insts = map clInst is
        match' :: Type -> Type -> Maybe (M.Map Name Type)
        match' (ConT x) t   = M.empty <$ (t^?_ConT.only x) 
        match' (VarT x) t   = Just $ M.singleton x t
        match' (AppT x y) t = (t^?_AppT) >>= \(x',y') -> M.union <$> match' x x' <*> match' y y'
        match' ArrowT t     = M.empty <$ (t^?_ArrowT)
        match' t t' = error $ [printf|\n%s\n%s\n|] (pprint t) (pprint t')
        match :: Type -> Type -> Type
        match t t' = fromMaybe t' $ t'^?_ForallT.to (\x -> withInt $ substType (M.unions $ mapMaybe (flip match' t) $ x^._2) (x^._3))
        clInst (InstanceD _ t _) = t
        clInst _ = undefined
        decName (SigD n _) = n
        decName _ = undefined
        subst :: Type -> Dec -> ExpQ
        subst m (SigD n t) = sigE (varE n) $ return $ match m t
        subst _ _ = undefined
        propName :: String -> ExpQ
        propName n = [| PropName $(stringE n) $(lift $ loc_filename loc) $(lift $ fst $ loc_start loc) |]
        quickCheckInvoke :: Type -> Dec -> ExpQ
        quickCheckInvoke t d = [e| (
            $(propName $ [printf|Axiom of %s : %s|] (pprint t) (nameBase $ decName d))
            , property $(subst t d)) |]
        props = quickCheckInvoke <$> insts <*> axioms
    when (null insts)  $ fail $ [printf|class %s does not have instances|] (show cl)
    when (null axioms) $ fail $ [printf|class %s does not have axioms|] (show cl)
    return props
