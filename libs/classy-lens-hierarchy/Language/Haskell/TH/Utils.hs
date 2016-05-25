module Language.Haskell.TH.Utils where

import Control.Arrow
import Control.Lens

import Data.Data
import Data.List as L
import Data.Maybe

import Language.Haskell.TH

import System.IO

printQ :: Ppr a => a -> Q a
printQ x = do
    runIO $ do
        putStrLn $ pprint x
        hFlush stdout
    return x

arrowType' :: [TypeQ] -> TypeQ -> TypeQ
arrowType' [] rt = rt
arrowType' (t:ts) rt = appsT [arrowT,t,arrowType' ts rt]

arrowType :: [Type] -> TypeQ -> TypeQ
arrowType = arrowType' . L.map return

appsT :: [TypeQ] -> TypeQ
appsT [] = error "empty type constructor"
appsT [x] = x
appsT (x:y:xs) = appsT (appT x y : xs) 

fieldList :: Info -> Q ([Name],Name,[(Name,Type)])
fieldList (TyConI (DataD _ _ args [RecC n cs] _)) = return (L.map name args,n,L.map f cs)
    where
        f (n,_,t) = (n,t)
        name (PlainTV n) = n
        name (KindedTV n _) = n
fieldList (TyConI (TySynD _n args t)) = do
        let (t',args') = fromMaybe (error "Bad constructor") $ constructor' t
        (xs,n',fs) <- fieldList =<< reify t'
        let sub = zip xs args'
            ys = drop (length args') xs
            name (KindedTV n _) = n
            name (PlainTV n) = n
        return $ (L.map name args ++ ys,n',L.map (second $ substVars' sub) fs)
fieldList _ = error "not a record type"

fieldType :: Type -> ([TyVarBndr],Type,Type)
fieldType (ForallT vs _ t) = (vs ++ ds,arg,ret)
    where
        (ds,arg,ret) = fieldType t
fieldType (AppT (AppT ArrowT arg) ret) = ([],arg,ret)
fieldType t = error $ "fieldType, invalid type: " ++ show t

substVars :: [(Name,Name)] -> Type -> Type
substVars ns = substVars' $ L.map (second VarT) ns

substVars' :: [(Name,Type)] -> Type -> Type
substVars' ns (VarT n) = fromMaybe (VarT n) (n `L.lookup` ns)
substVars' n t = runIdentity $ gfoldl f Identity t
    where
        f g t' = case cast t' of
                 Just t  -> g <*> Identity (fromJust $ cast $ substVars' n t)
                 Nothing -> g <*> Identity t'

constructor :: Type -> Name
constructor (ConT n)   = n
constructor (AppT t _) = constructor t
constructor ListT      = '[]
constructor t = error $ "not a simple type: " ++ show t

constructor' :: Type -> Maybe (Name,[Type])
constructor' (ConT n)    = Just (n,[])
constructor' (AppT t t') = second (++[t']) <$> constructor' t
constructor' ListT       = Just ('[],[])
constructor' (VarT _)    = Nothing
constructor' t = error $ "not a simple type: " ++ show t
