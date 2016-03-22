{-# LANGUAGE ConstraintKinds,ScopedTypeVariables #-}
module Data.Factory where

import Control.Lens
import Control.Monad

import Data.Existential
import Data.HashMap.Strict as M (HashMap,fromList,lookup,member)
import Data.Proxy
import Data.Proxy.TH
import Data.Serialize
import Data.Typeable

import GHC.Generics.Instances ()

import Language.Haskell.TH
import Language.Haskell.TH.Lens

import Text.Printf.TH

-- newtype Factory constr = Factory 
--         { runFactory :: forall r. TypeRep -> (forall a. (constr a, Typeable a) => Proxy a -> r) -> Maybe r }

type Factory constr = HashMap TypeRep (Cell1 Proxy constr)

runFactory :: Factory constr 
           -> TypeRep
           -> Maybe (Cell1 Proxy constr)
runFactory m trep = M.lookup trep m

class HasFactory constr where
    factory :: Proxy constr -> Factory constr

makeFactory :: Name -> DecsQ
makeFactory n = do
    t  <- varT $ mkName "a"
    ts <- reifyInstances n [t]
    tableName <- newName $ "table_" ++ nameBase n
    let ts' = filter (null.view _1) (ts^.instances) ^. types
        instances = partsOf (traverse._InstanceD)
        types = partsOf (traverse._2._AppT._2)
        sig = sigD tableName [t|Factory $(conT n)|]
        table = [e| fromList $(listE $ map pair ts') |]
        proxy :: Type -> ExpQ
        proxy t = [e| Proxy :: Proxy $(return t) |]
        pair :: Type -> ExpQ
        pair t = [e| (typeRep $(proxy t),Cell $ $(proxy t)) |]
        -- _ = ts' :: _
        dec = valD (varP tableName) (normalB table) []
    concat <$> sequenceA 
        [ sequenceA [sig,dec]
        , [d| instance HasFactory $(conT n) where 
                factory Proxy = $(varE tableName) |] ]
    -- [d| $(listE $ map (stringE . pprint) ts) |]

-- |
-- = Serialize Cells

putCell1 :: forall constr f. HasFactory constr
         => (forall a. constr a => Putter (f a))
         -> Putter (Cell1 f constr)
putCell1 putA (Cell x) = do
    let tr = [pr|constr|]
    unless (typeRep x `M.member` factory tr) $
        fail $ [printf|%s is not available in Factory (%s)|] (show $ typeRep x) (show tr)
    put (typeRep x) 
    putA x

getCell1 :: forall constr f. HasFactory constr
         => (forall a. constr a => Get (f a))
         -> Get (Cell1 f constr)
getCell1 f = do
        t <- get
        let _ = t :: TypeRep
            f' :: forall a. constr a => Proxy a -> Get (f a)
            f' _ = f
        maybe mzero (readCell1 $ fmap Cell . f') 
            $ runFactory (factory [pr|constr|]) t
