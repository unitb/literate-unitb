
{-# LANGUAGE ScopedTypeVariables
        , ExistentialQuantification
        , LambdaCase
        , KindSignatures
        #-}
module Document.VarScope where

    -- Modules
import Document.Phase.Types
import Document.Scope

import Logic.Expr

import UnitB.Syntax

    -- Libraries
import Control.Lens
import Control.Precondition

import           Data.Existential
import qualified Data.List.NonEmpty as NE
import           Data.Map.Class as M
import           Data.Typeable

import GHC.Generics.Instances

import Test.QuickCheck

import Text.Printf

import Utilities.Syntactic
import Utilities.Table

class (Typeable a,Scope a,PrettyPrintable a) => IsVarScope a where
    toOldEventDecl :: Name -> a -> [Either Error (EventId,[EventP2Field])]
    toNewEventDecl :: Name -> a -> [Either Error (EventId,[EventP2Field])]
    toThyDecl :: Name -> a -> [Either Error TheoryP2Field]
    toMchDecl :: Name -> a -> [Either Error (MachineP2'Field ae ce t)]

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
    rename_events' m = traverseCell' (rename_events' m)
    kind = readCell' kind

instance IsVarScope VarScope where
    toOldEventDecl s = readCell' $ toOldEventDecl s
    toNewEventDecl s = readCell' $ toNewEventDecl s
    toThyDecl s = readCell' $ toThyDecl s
    toMchDecl s = readCell' $ toMchDecl s

instance PrettyPrintable VarScope where
    pretty = readCell' pretty

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

data EvtDecls = Evt (Table (Maybe EventId) EventDecl)
    deriving (Eq,Ord,Show,Typeable,Generic)
    --         -- in Evt, 'Nothing' stands for a dummy

data EventDecl = EventDecl
    { _scope  :: EvtScope Var
    , _source :: NonEmpty EventId
    , _eventDeclDeclSource :: DeclSource
    , _eventDeclLineInfo   :: LineInfo 
    } deriving (Show,Eq,Ord,Generic)

data EvtScope a = Param a | Index a | Promoted (Maybe a)
    deriving (Eq,Ord,Generic,Functor,Show)

instance Eq VarScope where
    (==) = cellEqual' (==)

instance Ord VarScope where
    compare = cellCompare' compare


makeLenses ''EventDecl
makeFields ''EventDecl
makePrisms ''EvtScope

makeFields ''TheoryConst
makeFields ''TheoryDef
makeFields ''MachineVar
makeFields ''EvtDecls

varDecl :: Getter EventDecl (Maybe Var)
varDecl = scope.to (\case 
            Index v -> Just v
            Param v -> Just v
            Promoted v -> v)

declOf :: EvtScope var -> Maybe var
declOf (Index v) = Just v
declOf (Param v) = Just v
declOf (Promoted v) = v

instance Scope TheoryConst where
    kind _ = "constant"
    rename_events' _ e = [e]

instance Scope TheoryDef where
    kind _ = "constant"
    rename_events' _ e = [e]

instance Scope MachineVar where
    merge_scopes' (DelMch Nothing s _) (Machine v Inherited li) = Just $ DelMch (Just v) s li
    merge_scopes' (Machine v Inherited li) (DelMch Nothing s _) = Just $ DelMch (Just v) s li
    merge_scopes' _ _ = Nothing
    kind (DelMch _ _ _)   = "deleted variable"
    kind (Machine _ _ _)  = "state variable"
    rename_events' _ e = [e]

instance Scope EventDecl where
    kind x = case x^.scope of 
            Index _ -> "index"
            Param _ -> "parameter"
            Promoted _ -> "promoted parameter"
    keep_from s x | s == (x^.declSource) = Just x
                  | otherwise            = Nothing
    make_inherited = Just . (declSource .~ Inherited)
    merge_scopes' s0 s1 = case (s0^.scope,s1^.scope) of
            (Param v,Promoted Nothing) -> case s1^.declSource of
                    Inherited -> Just $ s1 
                        & scope .~ Index v
                        & declSource .~ Inherited
                    Local -> Just $ s1 
                        & scope .~ Promoted (Just v) 
                        & declSource .~ Inherited
            (Promoted Nothing,Param v) -> case s0^.declSource of
                    Inherited -> Just $ s0 
                        & scope .~ Index v 
                        & declSource .~ Inherited
                    Local -> Just $ s0 
                        & scope .~ Promoted (Just v) 
                        & declSource .~ Inherited
            _ -> Nothing
    rename_events' _ e = [e]

instance PrettyPrintable a => PrettyPrintable (EvtScope a) where
    pretty = show . fmap Pretty

instance Scope EvtDecls where
    kind (Evt m) = show $ M.map (view scope) m
    keep_from s (Evt m) 
            | M.null r  = Nothing
            | otherwise = Just $ Evt r
        where
            r = M.mapMaybe (keep_from s) m
            -- f x
            --     | s == (x^.declSource) = Just x
            --     | otherwise = Nothing
    make_inherited (Evt m) = fmap Evt $ f $ M.mapMaybe make_inherited m
        where
            f m | M.null m  = Nothing
                | otherwise = Just m
    error_item (Evt m) = fromJust' $ NE.nonEmpty $ ascElems $ mapWithKey msg m
        where
            msg (Just k) x = (printf "%s (event '%s')" (kind x) (pretty k) :: String, x^.lineInfo)
            msg Nothing x  = ("dummy", x^.lineInfo)
    merge_scopes' (Evt m0) (Evt m1) = Evt <$> scopeUnion merge_scopes' m0 m1
    rename_events' lookup (Evt vs) = Evt <$> concatMap f (toList vs)
        where
            f (Just eid,x) = [ singleton (Just e) $ setSource eid x | e <- lookup eid ]
            f (Nothing,x)  = [ singleton Nothing x ]
            setSource eid  = source .~ eid :| []

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

instance Arbitrary a => Arbitrary (EvtScope a) where
    arbitrary = genericArbitrary

