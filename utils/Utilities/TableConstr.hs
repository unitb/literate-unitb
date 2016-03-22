{-# LANGUAGE ConstraintKinds, TypeOperators #-}
module Utilities.TableConstr where

import Control.Arrow
import Control.Lens
import Control.Monad.Identity

import Data.Char
import Data.Data
import Data.Either
import Data.List as L
import Data.Map.Class as M (Map,fromList,union,IsMap)
import Data.Maybe

import GHC.Generics hiding (from,to)
import GHC.Generics.Lens

import Language.Haskell.TH

import System.IO

import Utilities.Table 
import Utilities.Table.HashKey
import Utilities.Table.BucketTable
import Utilities.Table.HashMap

prefix :: String -> Name -> Name
prefix p n = mkName $ prefix' p n

prefix' :: String -> Name -> String
prefix' p n = p ++ nameBase n

makeRecordConstr :: Name -> DecsQ
makeRecordConstr n = makeRecordConstrAs (prefix' "make" n) n

makeRecordConstrAs :: String -> Name -> DecsQ
makeRecordConstrAs makeName' n = do
    let makeName = mkName makeName'
    (args,cons,fields) <- fieldList =<< reify n
    xs <- newName "_xs"
    r  <- newName "r"
    x  <- newName "x"
    y  <- newName "y"
    let isMapType field t = case constructor' t of
                        Just (n,[t,t'])
                            | n == ''Map -> Right (field,(t, t'),n)
                            | n == ''Table -> Right (field,(t, t'),n)
                        _ -> Left (field,t)
        typeName  = mkName $ nameBase n ++ "Field"
        changeCap f x = mkName $ map f (take 1 x') ++ drop 1 x'
            where
                x' = nameBase x
        withUpper = changeCap toUpper . mkName . dropWhile (== '_') . nameBase
        fieldCons (n,(t,t'),_) = normalC (withUpper n) [strictType notStrict $ pure t,strictType notStrict $ pure t']
        fields'' = map (uncurry isMapType) fields
        fields' = rights fields''
        params  = lefts fields''
    params' <- forM params $ \v -> (v,) <$> newName "p"
    let fieldType = dataD (cxt []) typeName 
                (map PlainTV args) 
                (map fieldCons fields') 
                []
        fieldInit (n,(_t,_t'),_) = (n,) <$> [e| fromList (concatMap $(varE $ prefix "_" n) $(varE xs)) |]
        fieldGetter (n,(_t,_t'),_) = funD (prefix "_" n) 
                [ clause [conP (withUpper n) [varP x,varP y]] 
                    (normalB $ [e| [($(varE x), $(varE y))] |]) []
                , clause [wildP] (normalB $ listE []) []]
        paramInit ((f,_t),p) = (f,) <$> varE p
        fieldAsgn = map fieldInit fields'
        makeDef = recConE cons $ fieldAsgn ++ map paramInit params'
        make = funD makeName [clause 
            (map (varP . snd) params' ++ [varP xs]) 
            (normalB makeDef) 
            allGetters]
        allGetters = map fieldGetter fields'
        setterName = prefix "change" n
        setterSig = sigD setterName 
                    $ faType [t| $listType -> $recType -> $recType |]
        faType  = forallT 
                (map PlainTV args) (cxt []) 
        listType = [t| [ $(appsT $ conT typeName : argsT) ] |]
        recType = appsT $ conT n : argsT
        unionField (n,e) = (n,) <$> [e| M.union $(pure e) ($(varE n) $(varE r)) |]
        setterBody 
            | L.null fieldAsgn = varE r
            | otherwise        = recUpdE (varE r) $ (unionField =<<) <$> fieldAsgn
        setter  = funD setterName 
                    [ clause [varP xs,varP r] 
                      (normalB setterBody) 
                      allGetters ]
        argsT   = map varT args
        makeSig = sigD makeName $ faType
                $ arrowType (map (snd . fst) params') 
                    $ [t| $listType -> $recType |]
                    
    sequence 
        [ fieldType
        , makeSig
        , make
        , setterSig
        , setter]


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

substVars' :: [(Name,Type)] -> Type -> Type
substVars' ns (VarT n) = fromMaybe (VarT n) (n `L.lookup` ns)
substVars' n t = runIdentity $ gfoldl f Identity t
    where
        f g t' = case cast t' of
                 Just t  -> g <*> Identity (fromMaybe (error "bad constructor (2)") $ cast $ substVars' n t)
                 Nothing -> g <*> Identity t'

constructor' :: Type -> Maybe (Name,[Type])
constructor' (ConT n) = Just (n,[])
constructor' (AppT t t') = second (++[t']) <$> constructor' t
constructor' ListT       = Just ('[],[])
constructor' (VarT _)    = Nothing
constructor' t = error $ "not a simple type: " ++ show t

class GAllTables a where
    gAllTables :: (Applicative f)
               => (forall map k a. (Show k, Show a,IsMap map) => String -> map k a -> f (map k a))
               -> Maybe String -> a p -> f (a p)

instance (GAllTables c, Selector s) => GAllTables (S1 s c) where
    gAllTables f _ m@(M1 x) = M1 <$> gAllTables f (Just $ selName m) x

instance (GAllTables c) => GAllTables (D1 d c) where
    gAllTables f tag (M1 x) = M1 <$> gAllTables f tag x

instance (GAllTables c) => GAllTables (C1 d c) where
    gAllTables f tag (M1 x) = M1 <$> gAllTables f tag x

instance (Show k,Show b) => GAllTables (K1 a (MapWithHash k b)) where
    gAllTables f (Just tag) (K1 x) = K1 <$> f tag x
    gAllTables _ Nothing (K1 x) = K1 <$> pure x

instance (Show k,Show b) => GAllTables (K1 a (HashTable k b)) where
    gAllTables f (Just tag) (K1 x) = K1 <$> f tag x
    gAllTables _ Nothing (K1 x) = K1 <$> pure x

instance (Show k,Show b) => GAllTables (K1 a (HashMap k b)) where
    gAllTables f (Just tag) (K1 x) = K1 <$> f tag x
    gAllTables _ Nothing (K1 x) = K1 <$> pure x

instance (Show k,Show b) => GAllTables (K1 a (Map k b)) where
    gAllTables f (Just tag) (K1 x) = K1 <$> f tag x
    gAllTables _ Nothing (K1 x) = K1 <$> pure x

instance (GAllTables a, GAllTables b) 
        => GAllTables (a :*: b) where
    gAllTables f tag (x :*: y) = (:*:) <$> gAllTables f tag x <*> gAllTables f tag y

allTables :: (Applicative f, Generic x, GAllTables (Rep x))
          => (forall k a map. (Show k,Show a,IsMap map) => String -> map k a -> f (map k a))
          -> x -> f x
allTables f = generic $ gAllTables f Nothing

