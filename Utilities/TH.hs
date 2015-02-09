{-# LANGUAGE TemplateHaskell,QuasiQuotes,TupleSections #-}
{-# LANGUAGE RankNTypes #-}
module Utilities.TH where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Lens
-- import Control.Lens.TH
-- import Control.Lens.Internal.FieldTH

import Data.Char
import Data.Data hiding (typeOf)
import Data.List
import Data.Maybe
-- import Data.Time

import Language.Haskell.TH

-- import System.Locale
import System.IO

import Text.Printf


makePolyClass :: Name -> DecsQ
makePolyClass recName = do
    i <- reify recName
    (_rec,fs) <- fieldList i
    let base = nameBase recName
        lens = mkName "Lens"
        fT   = mkName "f"
        xT   = mkName "a"
        yT   = mkName "b"
        fV = varT fT
        xV = varT xT
        yV = varT yT
        ff x  = varT fT `appT` varT x
        typ x = conT recName `appT` varT x
        className  = mkName $ "Has" ++ base
        methodName = mkName $ map toLower (take 1 base) ++ drop 1 base
        methodE = varE methodName
        fieldName (f,_)
            | "_" `isPrefixOf` nameBase f = mkName $ drop 1 $ nameBase f
            | otherwise          = f
    polyClass  <- classD (return []) className [PlainTV fT] [] 
                    [ sigD methodName $ forallT [PlainTV xT, PlainTV yT] (return []) 
                        $ appsT [conT lens,ff xT,ff yT,typ xT,typ yT]
                    ]
    polyInstance <- instanceD (return []) (appT (conT className) (conT recName))
        [ funD methodName [clause [] (normalB $ varE 'id) []] 
        ]
    fields <- liftM concat
            $ forM (filter (("_" `isPrefixOf`) . nameBase . fst) fs) 
            $ \f -> sequence $
        [ funD (fieldName f) [clause [] 
                (normalB [e| $methodE . $(lensDecl recName (fst f)) |])
                []
                ]
        , let t
                | hasVars (snd f) = [t| Lens ($fV $xV) ($fV $yV) 
                                            $(return $ substVars xT $ snd f) 
                                            $(return $ substVars yT $ snd f) |]
                | otherwise       = [t| Lens' ($fV $xV) $(return $ snd f) |]
              typeVars
                | hasVars (snd f) = map PlainTV [fT,xT,yT]
                | otherwise       = map PlainTV [fT,xT]
          in 
          sigD (fieldName f) $ forallT typeVars
            (cxt [classP className [varT fT]]) t            
        ] -- substVars _ $ 
    -- runIO $ do
    --     h <- openFile "template.txt" AppendMode
    --     hPrintf h "%s\n%s\n%s\n" 
    --         (pprint polyClass)
    --         (pprint polyInstance)
    --         (unlines $ map pprint fields)
    --     hClose h
    return $ polyClass:polyInstance:fields

makeHierarchy :: Name -> [(Name,Name)] -> DecsQ
makeHierarchy ls xs' = do
    let xs = reverse xs'
        makeInstance (tn,fn) ns = do
            let ns' = uncurry zip $ (++ [ls]) *** (fn:) $ unzip ns
            liftM id $ forM ns' $ \(cn,fn) -> do
                let base = nameBase cn
                    classNameT = conT $ mkName $ "Has" ++ base
                    typeName   = conT tn
                    methodName = mkName $ map toLower (take 1 base) ++ drop 1 base
                instanceD (return []) [t| $classNameT $typeName |]
                    [ funD methodName [clause [] (normalB $ varE fn) []] 
                    ]
    xs <- concat <$> zipWithM makeInstance xs (drop 1 $ tails xs)
    -- runIO $ do
    --     printf "%s\n" 
    -- --         (pprint polyClass)
    -- --         (pprint polyInstance)
    --         (unlines $ map pprint xs)
    return xs    

substVars :: Name -> Type -> Type
substVars n (VarT _) = VarT n
substVars n t = runIdentity $ gfoldl f Identity t
    where
        f g t' = case cast t' of
                 Just t  -> g <*> Identity (fromJust $ cast $ substVars n t)
                 Nothing -> g <*> Identity t'

hasVars :: Type -> Bool
hasVars (VarT _) = True
hasVars t = getConst $ gfoldl f (const $ Const False) t
    where
        f (Const b) t' = case cast t' of
                 Just t -> (Const $ b || hasVars t)
                 Nothing -> Const b

appsT :: [TypeQ] -> TypeQ
appsT [] = error "empty type constructor"
appsT [x] = x
appsT (x:y:xs) = appsT (appT x y : xs) 

fieldType :: Type -> ([TyVarBndr],Type,Type)
fieldType (ForallT vs _ t) = (vs ++ ds,arg,ret)
    where
        (ds,arg,ret) = fieldType t
fieldType (AppT (AppT ArrowT arg) ret) = ([],arg,ret)
fieldType _ = error "invalid type"

constructor :: Type -> Name
constructor (ConT n) = n
constructor (AppT t _) = constructor t
constructor _ = error "not a simple type"

fieldList :: Info -> Q (Name,[(Name,Type)])
fieldList (TyConI (DataD _ _ _ [RecC n cs] _)) = return (n,map f cs)
    where
        f (n,_,t) = (n,t)
fieldList (TyConI (TySynD _ _ t)) =
        fieldList =<< reify (constructor t)
fieldList _ = error "not a record type"

typeOf :: Name -> TypeQ
typeOf n = do
    t <- reify n
    case t of
        VarI _ t _ _ -> return t
        _ -> error "not a variable"

lensDecl :: Name -> Name -> Q Exp
lensDecl t' n = do
    i <- reify t'
    (rec,fs) <- fieldList i
    let c = mkName "c"
        x = mkName "x"
        update c n x = appsE $ conE rec : map (f . fst) fs
            where
                f n'
                    | n' == n   = varE x
                    | otherwise = appE (varE n') (varE c)
    appE (appE (varE $ mkName "lens") $ varE n)
                (lamE [varP c,varP x] $ update c n x) 

mkLens :: Name -> ExpQ 
mkLens n = do
    t <- typeOf n
    let (_,at,_rt) = fieldType t
        t' = constructor at
    res <- lensDecl t' n  
    return res
