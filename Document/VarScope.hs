
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes,TupleSections  #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE DeriveDataTypeable        #-}
module Document.VarScope where

    -- Modules
import Document.Phase
import Document.Scope

import Logic.Expr hiding (Const)

import UnitB.AST

    -- Libraries
import Control.Applicative
import Control.Monad.Identity
import Control.Lens

import Data.Map as M
import Data.Maybe
import Data.Typeable

import Utilities.Format
import Utilities.HeterogenousEquality
import Utilities.Syntactic
import Utilities.TH

-- apply :: Functor f
--       => (forall a. IsVarScope a => a -> f a)
--       -> VarScope -> f VarScope
-- apply f (VarScope x) = VarScope <$> f x

-- apply2 :: Functor f
--        => (forall a. IsVarScope a => a -> a -> f a)
--        -> VarScope -> VarScope -> Maybe (f VarScope)
-- apply2 f (VarScope x) (VarScope y) = fmap VarScope <$> (f x <$> cast y)

class (Typeable a,Scope a) => IsVarScope a where
    toOldEventDecl :: String -> a -> [Either Error (EventId,[EventP2Field])]
    toNewEventDecl :: String -> a -> [Either Error (EventId,[EventP2Field])]
    toThyDecl :: String -> a -> [Either Error TheoryP2Field]
    toMchDecl :: String -> a -> [Either Error (MachineP2'Field b c)]

data VarScope = forall a. IsVarScope a => VarScope a
    deriving (Typeable)


existential ''VarScope

instance Scope VarScope where
    keep_from s = applyVarScope (keep_from s)
    make_inherited = applyVarScope make_inherited
    clashes = fmap (fromMaybe True . fmap getConst) . apply2VarScope (fmap Const . clashes)
    merge_scopes = fmap (runIdentity . fromJust) . apply2VarScope (fmap Identity . merge_scopes)
    error_item = readVarScope error_item
    rename_events m = applyVarScope (rename_events m)
    kind (VarScope v) = kind v

instance IsVarScope VarScope where
    toOldEventDecl s (VarScope v) = toOldEventDecl s v
    toNewEventDecl s (VarScope v) = toNewEventDecl s v
    toThyDecl s (VarScope v) = toThyDecl s v
    toMchDecl s (VarScope v) = toMchDecl s v

data TheoryConst = TheoryConst 
        { thCons :: Var
        , _theoryConstDeclSource :: DeclSource
        , _theoryConstLineInfo :: LineInfo }        
    deriving (Eq,Ord,Show,Typeable)

data TheoryDef = TheoryDef 
        { thDef :: Def
        , _theoryDefDeclSource :: DeclSource
        , _theoryDefLineInfo :: LineInfo }
    deriving (Eq,Ord,Show,Typeable)

data MachineVar = 
        Machine 
            { var :: Var
            , _machineVarDeclSource :: DeclSource
            , _machineVarLineInfo :: LineInfo }
        | DelMch 
            { mvar :: Maybe Var
            , _machineVarDeclSource :: DeclSource
            , _machineVarLineInfo :: LineInfo }
    deriving (Eq,Ord,Show,Typeable)

data EvtDecl = Evt (Map (Maybe EventId) (Var,EvtScope,DeclSource,LineInfo))
    deriving (Eq,Ord,Show,Typeable)
    --         -- in Evt, 'Nothing' stands for a dummy

instance Eq VarScope where
    VarScope x == VarScope y = h_equal x y

instance Ord VarScope where
    VarScope x `compare` VarScope y = h_compare x y

data EvtScope = Param | Index
    deriving (Eq,Ord)

instance Show EvtScope where
    show Param = "parameter"
    show Index = "index"

makeFields ''TheoryConst
makeFields ''TheoryDef
makeFields ''MachineVar
makeFields ''EvtDecl


instance Scope TheoryConst where
    kind _ = "constant"
    rename_events _ x = [x]

instance Scope TheoryDef where
    kind _ = "constant"
    rename_events _ x = [x]

instance Scope MachineVar where
    clashes (DelMch Nothing _ _) (Machine _ Inherited _) = False
    clashes (Machine _ Inherited _) (DelMch Nothing _ _) = False
    clashes _ _ = True
    merge_scopes (DelMch Nothing s _) (Machine v Inherited li) = DelMch (Just v) s li
    merge_scopes (Machine v Inherited li) (DelMch Nothing s _) = DelMch (Just v) s li
    merge_scopes _ _ = error "MachineVar Scope.merge_scopes: _, _"
    kind (DelMch _ _ _)   = "deleted variable"
    kind (Machine _ _ _)  = "state variable"
    rename_events _ x = [x]

instance Scope EvtDecl where
    kind (Evt m) = show $ M.map (view _2) m
    keep_from s (Evt m) 
            | M.null r  = Nothing
            | otherwise = Just $ Evt r
        where
            r = M.mapMaybe f m
            f x@(_,_,s',_)
                | s == s'   = Just x
                | otherwise = Nothing
    make_inherited (Evt m) = Just $ Evt $ M.map (set _3 Inherited) m
    clashes (Evt m0) (Evt m1) = not $ M.null $ m0 `M.intersection` m1
    error_item (Evt m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' [] = error "VarScope Scope VarScope: head' []"  
            head' _ = error "VarScope Scope VarScope: head' too many"
            msg (Just k) (_v,sc,_,li) = (format "{1} (event {0})" k (show sc) :: String, li)
            msg Nothing (_v,_,_,li) = (format "dummy", li)
    merge_scopes (Evt m0) (Evt m1) = Evt $ unionWith (error "VarScope Scope.merge_scopes: Evt, Evt") m0 m1
    rename_events m (Evt vs) = Evt <$> concatMap f (toList vs)
        where
            lookup x = fromMaybe [x] $ M.lookup x m
            f (Just eid,x) = [ singleton (Just e) x | e <- lookup eid ]
            f (Nothing,x)  = [ singleton Nothing x ]
