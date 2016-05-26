{-# LANGUAGE ConstraintKinds, TypeOperators #-}
module Data.MakeTable where

import Control.Lens
import Control.Monad.Identity

import Data.Char
import Data.Either
import Data.List as L
import Data.HashMap.Strict (HashMap)
import Data.Map.Class as M (Map,fromList,union,IsMap)

import GHC.Generics hiding (from,to)
import GHC.Generics.Lens

import Language.Haskell.TH
import Language.Haskell.TH.Lens
import Language.Haskell.TH.Utils

prefix :: String -> Name -> Name
prefix p n = mkName $ prefix' p n

prefix' :: String -> Name -> String
prefix' p n = p ++ nameBase n

makeRecordConstr :: Name -> DecsQ
makeRecordConstr n = makeRecordConstrAs (prefix' "make" n) n

expandTySyn :: Name -> Q Name
expandTySyn n = maybe (return n) expandTySyn . getTySyn =<< reify n
    where
        getTySyn = preview (_TyConI . _TySynD . _3 . to constructor)

makeRecordConstrAs :: String -> Name -> DecsQ
makeRecordConstrAs makeName' n = do
    let makeName = mkName makeName'
    (args,cons,fields) <- fieldList =<< reify n
    xs <- newName "_xs"
    r  <- newName "r"
    x  <- newName "x"
    y  <- newName "y"
    let isMapType field t = do
                    r <- constructor' t & (traverse._1) expandTySyn
                    return $ case r of
                        Just (n,[t,t'])
                            | n == ''Map -> Right (field,(t, t'),n)
                            | n == ''HashMap -> Right (field,(t, t'),n)
                        _ -> Left (field,t)
        typeName  = mkName $ nameBase n ++ "Field"
        changeCap f x = mkName $ map f (take 1 x') ++ drop 1 x'
            where
                x' = nameBase x
        withUpper = changeCap toUpper . mkName . dropWhile (== '_') . nameBase
        fieldCons (n,(t,t'),_) = normalC (withUpper n) [strictType notStrict $ pure t,strictType notStrict $ pure t']
    fields'' <- mapM (uncurry isMapType) fields
    let fields' = rights fields''
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

