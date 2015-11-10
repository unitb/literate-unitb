
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables, KindSignatures
       #-}
module Document.VarScope where

    -- Modules
import Document.Phase
import Document.Scope

import Logic.Expr hiding (Const)

import UnitB.AST

    -- Libraries
import Control.Lens

import Data.List.NonEmpty (NonEmpty(..))
import Data.Map as M
import Data.Maybe
import Data.Typeable

import Test.QuickCheck

import Utilities.Existential
import Utilities.Format
import Utilities.Instances
import Utilities.Syntactic

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

newtype VarScope = VarScope { _varScopeCell :: Cell IsVarScope }
    deriving (Typeable)

makeFields ''VarScope

instance Show VarScope where
    show = readCell' show

instance Scope VarScope where
    keep_from s = traverseCell' (keep_from s)
    make_inherited = traverseCell' make_inherited
    merge_scopes' = -- fmap (runIdentity . fromJust) . 
        apply2Cells' merge_scopes' Nothing
    error_item = readCell' error_item
    rename_events m = traverseCell' (rename_events m)
    kind = readCell' kind

instance IsVarScope VarScope where
    toOldEventDecl s = readCell' $ toOldEventDecl s
    toNewEventDecl s = readCell' $ toNewEventDecl s
    toThyDecl s = readCell' $ toThyDecl s
    toMchDecl s = readCell' $ toMchDecl s

data TheoryConst = TheoryConst 
        { thCons :: Var
        , _theoryConstDeclSource :: DeclSource
        , _theoryConstLineInfo :: LineInfo }        
    deriving (Eq,Ord,Show,Typeable,Generic)

data TheoryDef = TheoryDef 
        { thDef :: Def
        , _theoryDefDeclSource :: DeclSource
        , _theoryDefLineInfo :: LineInfo }
    deriving (Eq,Ord,Show,Typeable,Generic)

data MachineVar = 
        Machine 
            { var :: Var
            , _machineVarDeclSource :: DeclSource
            , _machineVarLineInfo :: LineInfo }
        | DelMch 
            { mvar :: Maybe Var
            , _machineVarDeclSource :: DeclSource
            , _machineVarLineInfo :: LineInfo }
    deriving (Eq,Ord,Show,Typeable,Generic)

data EvtDecls = Evt (Map (Maybe EventId) EventDecl)
    deriving (Eq,Ord,Show,Typeable,Generic)
    --         -- in Evt, 'Nothing' stands for a dummy

data EventDecl = EventDecl
    { _eventDeclVarDecl :: Var
    , _scope :: EvtScope
    , _source :: NonEmpty EventId
    , _eventDeclDeclSource :: DeclSource
    , _eventDeclLineInfo :: LineInfo 
    } deriving (Show,Eq,Ord,Generic)

data EvtScope = Param | Index
    deriving (Eq,Ord,Generic)

instance Eq VarScope where
    (==) = cellEqual' (==)

instance Ord VarScope where
    compare = cellCompare' compare

instance Show EvtScope where
    show Param = "parameter"
    show Index = "index"

makeLenses ''EventDecl
makeFields ''EventDecl

makeFields ''TheoryConst
makeFields ''TheoryDef
makeFields ''MachineVar
makeFields ''EvtDecls

-- groupVars :: [VarGroup] -> [VarGroup]
-- groupVars vs = g $ sortOn f vs
--     where
--         f (VarGroup x) = typeRep x
--         g (VarGroup xs:VarGroup ys:vs) = case cast ys of
--                                             Just ys -> g $ (VarGroup $ xs ++ ys):vs
--                                             Nothing -> VarGroup xs : g (VarGroup ys : vs)
--         g vs = vs

instance Scope TheoryConst where
    kind _ = "constant"
    rename_events _ x = [x]

instance Scope TheoryDef where
    kind _ = "constant"
    rename_events _ x = [x]

instance Scope MachineVar where
    merge_scopes' (DelMch Nothing s _) (Machine v Inherited li) = Just $ DelMch (Just v) s li
    merge_scopes' (Machine v Inherited li) (DelMch Nothing s _) = Just $ DelMch (Just v) s li
    merge_scopes' _ _ = Nothing
    kind (DelMch _ _ _)   = "deleted variable"
    kind (Machine _ _ _)  = "state variable"
    rename_events _ x = [x]

instance Scope EvtDecls where
    kind (Evt m) = show $ M.map (view scope) m
    keep_from s (Evt m) 
            | M.null r  = Nothing
            | otherwise = Just $ Evt r
        where
            r = M.mapMaybe f m
            f x
                | s == (x^.declSource) = Just x
                | otherwise = Nothing
    make_inherited (Evt m) = Just $ Evt $ M.map (set declSource Inherited) m
    error_item (Evt m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' [] = error "VarScope Scope VarScope: head' []"  
            head' _ = error "VarScope Scope VarScope: head' too many"
            msg (Just k) x = (format "{1} (event '{0}')" k (show $ x^.scope) :: String, x^.lineInfo)
            msg Nothing x  = (format "dummy", x^.lineInfo)
    merge_scopes' (Evt m0) (Evt m1) = Evt <$> scopeUnion (const $ const Nothing) m0 m1
    rename_events m (Evt vs) = Evt <$> concatMap f (toList vs)
        where
            lookup x = fromMaybe [x] $ M.lookup x m
            f (Just eid,x) = [ singleton (Just e) $ setSource eid x | e <- lookup eid ]
            f (Nothing,x)  = [ singleton Nothing x ]
            setSource eid x = x & source .~ eid :| []

instance Arbitrary TheoryDef where
    arbitrary = genericArbitrary

instance Arbitrary TheoryConst where
    arbitrary = genericArbitrary

instance Arbitrary MachineVar where
    arbitrary = genericArbitrary

instance Arbitrary EventDecl where
    arbitrary = genericArbitrary

instance Arbitrary EvtDecls where
    arbitrary = Evt . fromList <$> arbitrary

instance Arbitrary EvtScope where
    arbitrary = genericArbitrary

