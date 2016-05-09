module Test.QuickCheck.AxiomaticClass where

import Control.Lens
import Control.Monad

import Data.List
import qualified Data.Map as M
import Data.Maybe

import Prelude hiding (Monoid(..))

import Language.Haskell.TH
import Language.Haskell.TH.Lens

import Test.QuickCheck

import Text.Printf

    -- Copied from Test.QuickCheck.All
runQuickCheckAll :: [(String, Property)] -> (Property -> IO Result) -> IO Bool
runQuickCheckAll ps qc =
  fmap and . forM ps $ \(xs, p) -> do
    putStrLn $ "=== " ++ xs ++ " ==="
    r <- qc p
    putStrLn ""
    return $ case r of
      Success { } -> True
      Failure { } -> False
      NoExpectedFailure { } -> False
      GaveUp { } -> False
      InsufficientCoverage { } -> False

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
quickCheckClasses cls = do
    props <- concat <$> mapM quickCheckClassTests cls
    [e| runQuickCheckAll $(listE props) quickCheckResult |]

quickCheckClass :: Name -> ExpQ
quickCheckClass cl = do
    props <- quickCheckClassTests cl
    [e| runQuickCheckAll $(listE props) quickCheckResult |]

quickCheckClassTests :: Name -> Q [ExpQ]
quickCheckClassTests cl = do
    ClassI (ClassD _ _ args _ ms) is <- reify cl
    let axioms = filter (maybe False (isPrefixOf "axiom_") . nameOf) ms
        nameOf (SigD n _) = Just $ nameBase n
        nameOf _ = Nothing
        _ = args
        _ = insts

        insts = map clInst is
        --match' (t:ts) (AppT ts' t') = M.insert (t^.name) t' $ match ts ts'
        --match' _ _ = M.empty
        --match = match' . reverse
        --withInt (VarT x) = ConT ''Integer
        --withInt t = t & types %~ withInt
        match' :: Type -> Type -> Maybe (M.Map Name Type)
        match' (ConT x) t   = M.empty <$ (t^?_ConT.only x) 
        match' (VarT x) t   = Just $ M.singleton x t
        match' (AppT x y) t = (t^?_AppT) >>= \(x',y') -> M.union <$> match' x x' <*> match' y y'
        match' ArrowT t     = M.empty <$ (t^?_ArrowT)
        match' t t' = error $ printf "\n%s\n%s\n" (pprint t) (pprint t')
        --match'' t t' = trace (printf "-- %s - %s - %s" (show m) (show t) (show t')) m
        --    where m = match'' t t'
        match :: Type -> Type -> Type
        match t t' = fromMaybe t' $ t'^?_ForallT.to (\x -> withInt $ substType (M.unions $ mapMaybe (flip match' t) $ x^._2) (x^._3))
        clInst (InstanceD _ t _) = t
        clInst _ = undefined
        decName (SigD n _) = n
        decName _ = undefined
        subst :: Type -> Dec -> ExpQ
        subst m (SigD n t) = sigE (varE n) $ return $ match m t
        subst _ _ = undefined
        quickCheckInvoke :: Type -> Dec -> ExpQ
        quickCheckInvoke t d = [e| (
            $(stringE $ printf "Axiom of %s : %s" (pprint t) (nameBase $ decName d))
            , property $(subst t d)) |]
        props = quickCheckInvoke <$> insts <*> axioms
    when (null insts) $ fail $ printf "class %s does not have instances"
    when (null axioms) $ fail $ printf "class %s does not have axioms"
    return props
    --[e| runQuickCheckAll $(listE props) quickCheckResult |]
    --return [])
