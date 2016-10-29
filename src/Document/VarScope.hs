
{-# LANGUAGE ScopedTypeVariables
        , ExistentialQuantification
        , LambdaCase
        , KindSignatures
        #-}
module Document.VarScope where

    -- Modules
import Document.Phase.Types
import Document.Scope

import Latex.Parser (uncurry3)

import Logic.Expr

import UnitB.Syntax

    -- Libraries
import qualified Control.Invariant as I
import Control.Lens
import Control.Precondition

import           Data.Existential
import           Data.Hashable
import qualified Data.List.NonEmpty as NE
import           Data.Map as M
import           Data.Typeable

import GHC.Generics.Instances

import Test.QuickCheck
import Test.QuickCheck.Regression
import Test.QuickCheck.Report
import Test.QuickCheck.ZoomEq

import Text.Printf.TH

import Utilities.Syntactic

class (Typeable a,Scope a,PrettyPrintable a) => IsVarScope a where
    toOldEventDecl :: Name -> a -> [Either Error (EventId,[EventP2Field])]
    toNewEventDecl :: Name -> a -> [Either Error (EventId,[EventP2Field])]
    toThyDecl :: Name -> a -> [Either Error TheoryP2Field]
    toMchDecl :: Name -> a -> [Either Error (MachineP2'Field ae ce t)]

newtype VarScope = VarScope { _varScopeCell :: Cell IsVarScope }
    deriving (Typeable,Generic)

makeFields ''VarScope

instance Show VarScope where
    show = readCell' show

instance ZoomEq VarScope where
    x .== y = read2CellsWith' (.==) (x I.=== y) x y

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
        MchVar
            { var :: Var
            , _machineVarDeclSource :: DeclSource
            , _machineVarLineInfo :: LineInfo }
        | DelMchVar 
            { mvar :: Maybe Var
            , _machineVarDeclSource :: DeclSource
            , _machineVarLineInfo :: LineInfo }
    deriving (Eq,Ord,Show,Typeable,Generic)

data MachineDef = MchDef 
            { _machineDefName :: Name 
            , _term :: StringLi
            , _machineDefDeclSource :: DeclSource 
            , _machineDefLineInfo :: LineInfo }
    deriving (Eq,Ord,Show,Typeable,Generic)

data EvtDecls = Evt (Map EventOrDummy EventDecl)
    deriving (Eq,Ord,Show,Typeable,Generic)
    --         -- in Evt, 'Nothing' stands for a dummy

data DummyDecl = DummyDecl
    deriving (Eq,Ord,Show,Generic)

type EventOrDummy = Either DummyDecl EventId

data EventDecl = EventDecl
    { _scope  :: EvtScope Var
    , _source :: NonEmpty EventOrDummy
    , _eventDeclDeclSource :: DeclSource
    , _eventDeclLineInfo   :: LineInfo 
    } deriving (Show,Eq,Ord,Generic)

data EvtScope a = Param a | Index (InhStatus a) | Promoted (Maybe a)
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
makeFields ''MachineDef
makeFields ''EvtDecls

varDecl :: Getter EventDecl (Maybe Var)
varDecl = scope.to declOf

declOf :: EvtScope var -> Maybe var
declOf (Index (InhAdd v))    = Just v
declOf (Index (InhDelete v)) = v
declOf (Param v)    = Just v
declOf (Promoted v) = v

instance PrettyRecord TheoryConst where
instance PrettyPrintable TheoryConst where
    pretty = prettyRecord
instance ZoomEq TheoryConst where
instance Scope TheoryConst where
    kind _ = "constant"
    rename_events' _ e = [e]

instance PrettyRecord TheoryDef where
instance PrettyPrintable TheoryDef where
    pretty = prettyRecord
instance ZoomEq TheoryDef where
instance Scope TheoryDef where
    kind _ = "constant"
    rename_events' _ e = [e]

instance PrettyRecord MachineDef where
instance PrettyPrintable MachineDef where
    pretty = prettyRecord
instance ZoomEq MachineDef where
instance Scope MachineDef where
    kind _ = "definition"
    rename_events' _ e = [e]

instance PrettyRecord MachineVar where
instance PrettyPrintable MachineVar where
    pretty = prettyRecord
instance ZoomEq MachineVar where
instance Scope MachineVar where
    merge_scopes' (DelMchVar Nothing s _) (MchVar v Inherited li) = Just $ DelMchVar (Just v) s li
    merge_scopes' (MchVar v Inherited li) (DelMchVar Nothing s _) = Just $ DelMchVar (Just v) s li
    merge_scopes' _ _ = Nothing
    kind (DelMchVar _ _ _)   = "deleted variable"
    kind (MchVar _ _ _)  = "state variable"
    rename_events' _ e = [e]

instance PrettyRecord EventDecl where
instance PrettyPrintable EventDecl where
    pretty = prettyRecord
instance ZoomEq DummyDecl where
    (.==) = (I.===)
instance ZoomEq EventDecl where
instance Scope EventDecl where
    kind x = case x^.scope of 
            Index _ -> "index"
            Param _ -> "parameter"
            Promoted _ -> "promoted parameter"
    keep_from s x | s == (x^.declSource) = Just x
                  | otherwise            = Nothing
    make_inherited = Just . (declSource .~ Inherited)
    merge_scopes' s0 s1 = case (s0^.scope,s1^.scope) of
            (Index (InhAdd v),Index (InhDelete Nothing)) -> 
                    Just $ s1 
                        & scope .~ Index (InhDelete (Just v))
                        & source .~ s0^.source
                        -- & declSource %~ declUnion (s0^.declSource)
            (Index (InhDelete Nothing),Index (InhAdd v)) -> 
                    Just $ s0
                        & scope .~ Index (InhDelete (Just v))
                        & source .~ s1^.source
                        -- & declSource %~ declUnion (s1^.declSource)
            (Param v,Promoted Nothing) -> Just $ s1
                        & scope .~ Promoted (Just v)
                        & source .~ s0^.source
            (Promoted Nothing,Param v) -> Just $ s0
                        & scope .~ Promoted (Just v) 
                        & source .~ s1^.source
            _ -> Nothing
    rename_events' _ e = [e]

instance PrettyPrintable a => PrettyPrintable (EvtScope a) where
    pretty = show . fmap Pretty

instance PrettyPrintable DummyDecl where
    pretty DummyDecl = "dummy declaration"

instance Hashable DummyDecl where

instance PrettyPrintable EvtDecls where
    pretty (Evt e) = "Evt " ++ pretty e
instance ZoomEq EvtDecls where
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
    error_item (Evt m) = fromJust' $ NE.nonEmpty $ elems $ mapWithKey msg m
        where
            msg (Right k) x = ([s|%s (event '%s')|] (kind x) (pretty k), x^.lineInfo)
            msg (Left DummyDecl) x  = ("dummy", x^.lineInfo)
    merge_scopes' (Evt m0) (Evt m1) = Evt <$> scopeUnion merge_scopes' m0 m1
    rename_events' lookup (Evt vs) = Evt <$> concatMap f (toList vs)
        where
            f (Right eid,x) = [ singleton (Right e) $ setSource (Right eid) x | e <- lookup eid ]
            f (Left DummyDecl,x)  = [ singleton (Left DummyDecl) x ]
            setSource eid  = source .~ eid :| []

instance Arbitrary TheoryDef where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary TheoryConst where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary MachineVar where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary MachineDef where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary EventDecl where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary DummyDecl where
    arbitrary = return DummyDecl

instance Arbitrary EvtDecls where
    arbitrary = Evt . fromList <$> arbitrary
    shrink = genericShrink

instance ZoomEq a => ZoomEq (EvtScope a) where
instance Arbitrary a => Arbitrary (EvtScope a) where
    arbitrary = genericArbitrary
    shrink = genericShrink

prop_axiom_Scope_clashesOverMerge :: Property
prop_axiom_Scope_clashesOverMerge = regression (uncurry3 axiom_Scope_clashesOverMerge) 
        [ (x,y,z) ]
    where
        x = Evt (fromList [(Left DummyDecl,EventDecl {_scope = Param (Var (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) (Gen (DefSort (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) (InternalName "" (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) "") [] (Gen (Sort (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) (InternalName "" (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) "") 0) [])) [])), _source = Right (EventId (Lbl "m")) :| [], _eventDeclDeclSource = Local, _eventDeclLineInfo = (LI "file" 0 0)})])
        y = Evt (fromList [(Left DummyDecl,EventDecl {_scope = Promoted Nothing, _source = Right (EventId (Lbl "c")) :| [], _eventDeclDeclSource = Inherited, _eventDeclLineInfo = (LI "file" 0 0)})])
        z = Evt (fromList [(Left DummyDecl,EventDecl {_scope = Index (InhDelete Nothing), _source = Right (EventId (Lbl "c")) :| [], _eventDeclDeclSource = Local, _eventDeclLineInfo = (LI "file" 0 10)})])

return []

run_tests :: (PropName -> Property -> IO (a, Result))
          -> IO ([a], Bool)
run_tests = $forAllProperties'

