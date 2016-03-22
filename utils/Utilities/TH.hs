{-# LANGUAGE QuasiQuotes #-}
module Utilities.TH where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Fix
import Control.Lens
-- import Control.Lens.TH
-- import Control.Lens.Internal.FieldTH

import Data.Char
import Data.Data hiding (typeOf)
import Data.Data.Lens
import Data.Default
import Data.Graph
import Data.Graph.Array
import Data.List as L
import Data.List.Ordered
import Data.Map as M
import Data.Maybe
import Data.Tuple
import Data.Typeable.Lens

import Language.Haskell.TH

import Text.Printf


makePolyClass :: Name -> DecsQ
makePolyClass recName = do
    i <- reify recName
    (args,_rec,fs) <- fieldList i
    let base = nameBase recName
        lens = mkName "Lens"
        fT   = mkName "f"
        xT   = L.map (mkName . printf "a%d") [0..length args-1]
        yT   = L.map (mkName . printf "b%d") [0..length args-1]
        fV = varT fT
        xV = L.map varT xT
        -- yV = L.map varT yT
        ff x  = appsT $ varT fT : L.map varT x
        typ x = appsT $ conT recName : L.map varT x
        className  = mkName $ "Has" ++ base
        methodName = mkName $ L.map toLower (take 1 base) ++ drop 1 base
        methodE = varE methodName
        fieldName (f,_)
            | "_" `isPrefixOf` nameBase f = mkName $ drop 1 $ nameBase f
            | otherwise          = f
    polyClass  <- classD (return []) className [PlainTV fT] [] 
                    [ sigD methodName $ forallT (L.map PlainTV $ xT ++ yT) (return []) 
                        $ appsT [conT lens,ff xT,ff yT,typ xT,typ yT]
                    ]
    polyInstance <- instanceD (return []) (appT (conT className) (conT recName))
        [ funD methodName [clause [] (normalB $ varE 'id) []] 
        ]
    fields <- liftM concat
            $ forM (L.filter (("_" `isPrefixOf`) . nameBase . fst) fs) 
            $ \f -> sequence $
        [ funD (fieldName f) [clause [] 
                (normalB [e| $methodE . $(lensDecl recName (fst f)) |])
                []
                ]
        , let 
              mX = (zip args xT)
              mY = (zip args yT)
              zT = zipWith3 (\k x y -> if k `elem` fv then y else x) args xT yT
              zV = L.map varT zT
              fv = freeVars (snd f)
              t = [t| Lens $(appsT $ fV : xV) $(appsT $ fV : zV) 
                -- | hasVars (snd f) 
                                            $(return $ substVars mX $ snd f) 
                                            $(return $ substVars mY $ snd f) |]
                -- | otherwise       = [t| Lens' $(appsT $ fV : xV) $(return $ snd f) |]
              typeVars = L.map PlainTV $ fT : (nubSort $ xT++zT)
                -- | hasVars (snd f) 
                -- | otherwise       = L.map PlainTV $ fT : xT
          in 
          sigD (fieldName f) $ forallT typeVars
            (cxt [appT (conT className) (varT fT)]) t            
        ] -- substVars _ $ 
    return $ polyClass:polyInstance:fields

createHierarchy :: [(Name,Name)] -> DecsQ
createHierarchy xs = do
    let f (_,_,x) = constructor x
    graph <- forM xs $ \(t,field) -> do
        t' <- typeOf field
        return (t,f $ fieldType t')
    let vs = nubSort $ uncurry (++) $ unzip graph
        ord = L.map flat $ top_sort vs graph
        dropUS x = mkName $ drop 1 $ nameBase x
        edges = fromListWith (++) $ zipWith (\(k,f) (_,t) -> (k,[(dropUS f,t)])) xs graph
                    ++ zip vs (repeat [])
        flat (AcyclicSCC v) = v
        flat (CyclicSCC vs) = error $ printf "A cycle exists in the inheritance\
                                    \ relation %s" $ intercalate "," (L.map show vs)
        proc n m = adjust (\xs -> xs ++ concatMap ((m !) . snd) xs) n m
        ancestors = L.foldr proc edges ord 
    -- runIO $ do
    --     forM_ (toList ancestors) $ \(k,xs) -> do
    --         printf "%s: %s\n" (show k) (intercalate "," $ L.map (show . snd) xs)
    decs <- liftM (concat . concat) $ sequence 
        [ forM (toList $ M.map (L.map swap) ancestors) 
            $ uncurry makeInstance 
        , mapM makePolyClass $ keys ancestors ]
    return decs

makeInstance :: Name -> [(Name, Name)] -> Q [Dec]
makeInstance tn cs =
    forM cs $ \(cn,fn) -> do
        let base = nameBase cn
            classNameT = conT $ mkName $ "Has" ++ base
            typeName   = conT tn
            methodName = mkName $ L.map toLower (take 1 base) ++ drop 1 base
        ck <- typeKind cn
        tk <- typeKind tn
        let n = L.map (varT . mkName . (:[])) $ take (tk - ck) ['a'..]
        instanceD (return []) [t| $classNameT $(appsT $ typeName : n) |]
            [ funD methodName [clause [] (normalB $ varE fn) []] 
            ]

makeHierarchy :: Name -> [(Name,Name)] -> DecsQ
makeHierarchy ls xs' = do
    let xs = reverse xs'
        makeInstance' (tn,fn) ns = do
            let ns' = uncurry zip $ (++ [ls]) *** (fn:) $ unzip ns
            makeInstance tn ns'
    xs <- concat <$> zipWithM makeInstance' xs (drop 1 $ tails xs)
    -- runIO $ do
    --     printf "%s\n" 
    -- --         (pprint polyClass)
    -- --         (pprint polyInstance)
    --         (unlines $ L.map pprint xs)
    return xs    

classKind :: Name -> Q Int
classKind n = do
    i <- reify n
    case i of 
        ClassI (ClassD _ _ [KindedTV _ arg] _ _) _ -> return $ arity arg
        ClassI (ClassD _ _ [PlainTV _] _ _) _ -> return 0
        ClassI (ClassD _ _ [] _ _) _ -> fail "too many class parameters"
        _ -> fail $ printf "invalid class: %s %s" (show n) (show i)
    where
        arity (AppT (AppT ArrowT _) k) = 1 + arity k
        arity StarT = 0
        arity _ = error "invalid kind"

typeKind :: Name -> Q Int
typeKind n = do
        i <- reify n
        case i of 
            TyConI (DataD _ _ args _ _) -> return $ length args
            TyConI (NewtypeD _ _ args _ _) -> return $ length args
            TyConI (TySynD _ _ t) -> do
                n <- degree t
                return n
            _ -> fail $ printf "typeKind, invalid type: %s\n%s" (show n) (show i)
    where
        degree (AppT t0 _) = (-1 +) <$> degree t0
        degree (ConT n) = typeKind n
        degree t = error $ "degree, invalid type: " ++ pprint t

substVars :: [(Name,Name)] -> Type -> Type
substVars ns = substVars' $ L.map (second VarT) ns

substVars' :: [(Name,Type)] -> Type -> Type
substVars' ns (VarT n) = fromMaybe (VarT n) (n `L.lookup` ns)
substVars' n t = runIdentity $ gfoldl f Identity t
    where
        f g t' = case cast t' of
                 Just t  -> g <*> Identity (fromJust $ cast $ substVars' n t)
                 Nothing -> g <*> Identity t'

hasVars :: Type -> Bool
hasVars = not . L.null . freeVars

freeVars :: Type -> [Name]
freeVars (VarT n) = [n]
freeVars t = nubSort $ getConst $ gfoldl f (const $ Const []) t
    where
        f (Const xs) t' = case cast t' of
                 Just t -> (Const $ freeVars t ++ xs)
                 Nothing -> Const xs

appsT :: [TypeQ] -> TypeQ
appsT [] = error "empty type constructor"
appsT [x] = x
appsT (x:y:xs) = appsT (appT x y : xs) 

fieldType :: Type -> ([TyVarBndr],Type,Type)
fieldType (ForallT vs _ t) = (vs ++ ds,arg,ret)
    where
        (ds,arg,ret) = fieldType t
fieldType (AppT (AppT ArrowT arg) ret) = ([],arg,ret)
fieldType t = error $ "fieldType, invalid type: " ++ show t

constructor :: Type -> Name
constructor (ConT n) = n
constructor (AppT t _) = constructor t
constructor t = error $ "not a simple type: " ++ show t

constructor' :: Type -> (Name,[Type])
constructor' (ConT n) = (n,[])
constructor' (AppT t t') = second (++[t']) $ constructor' t
constructor' t = error $ "not a simple type: " ++ show t

fieldList :: Info -> Q ([Name],Name,[(Name,Type)])
fieldList (TyConI (DataD _ _ args [RecC n cs] _)) = return (L.map name args,n,L.map f cs)
    where
        f (n,_,t) = (n,t)
        name (PlainTV n) = n
        name (KindedTV n _) = n
fieldList (TyConI (TySynD _n args t)) = do
        let (t',args') = constructor' t
        (xs,n',fs) <- fieldList =<< reify t'
        let sub = zip xs args'
            ys = drop (length args') xs
            name (KindedTV n _) = n
            name (PlainTV n) = n
        return $ (L.map name args ++ ys,n',L.map (second $ substVars' sub) fs)
fieldList _ = error "not a record type"

typeOf :: Name -> TypeQ
typeOf n = do
    t <- reify n
    case t of
        VarI _ t _ _ -> return t
        _ -> error "not a variable"

lensDecl :: Name -> Name -> ExpQ
lensDecl t' n = do
    i <- reify t'
    (_,rec,fs) <- fieldList i
    c <- newName "_c"
    let x = mkName "x"
        update c n x = appsE $ conE rec : L.map (f . fst) fs
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

arrowType' :: [TypeQ] -> TypeQ -> TypeQ
arrowType' [] rt = rt
arrowType' (t:ts) rt = appsT [arrowT,t,arrowType' ts rt]

arrowType :: [Type] -> TypeQ -> TypeQ
arrowType = arrowType' . L.map return

mkCons :: Name -> DecsQ
mkCons n = do
    let cname = mkName $ "make" ++ nameBase n
    mkCons' n cname

mkCons' :: Name -> Name -> DecsQ
mkCons' n cname = do
    (ps,cons,fs) <- fieldList =<< reify n
    let p = recover (return False) . isInstance ''Default . (:[]) . snd
    defs <- filterM p fs
    args <- filterM (fmap not . p) fs
    let argNames = L.map (mkName . nameBase . fst) args
    let dinit = L.map (second $ const $ VarE 'def) defs
        arg_init = zip (L.map fst args) (L.map VarE argNames)
        val = RecConE cons (dinit ++ arg_init)
        decl = FunD cname [Clause (L.map VarP argNames) (NormalB val) []]
    tdecl <- sigD cname (forallT (L.map PlainTV ps) (return []) 
                $ arrowType (L.map snd args) (appsT $ conT n : L.map varT ps))
    return [tdecl,decl]
 
cons :: Name -> ExpQ
cons n = do
        xs <- L.map return <$> mkCons n 
        letE xs (varE cname)
    where
        cname = mkName $ "make" ++ nameBase n


count_cases :: DecsQ
count_cases = do
    n <- fix (\rec i -> do
        x <- lookupValueName $ "result" ++ show i
        case x of
            Just _  -> rec $ i + 1
            Nothing -> return i
        ) (0 :: Int)
    runIO $ printf "%d test cases\n" n
    return []

subexp :: Traversal' Exp Exp
subexp f = gtraverse (_cast f)

_FunType :: Prism' Type ([TyVarBndr], Cxt, Type, Type)
_FunType = prism cons isFun
    where
        cons ([],[],t0,t1) = AppT ArrowT t0 `AppT` t1
        cons (vs,cs,t0,t1) = ForallT vs cs $ AppT ArrowT t0 `AppT` t1
        isFun (ForallT vs cs (AppT (AppT ArrowT t0) t1)) = Right (vs,cs,t0,t1)
        isFun (AppT (AppT ArrowT t0) t1) = Right ([],[],t0,t1)
        isFun t = Left t

