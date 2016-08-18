
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
import qualified Data.List.NonEmpty as NE
import           Data.Map.Class as M
import           Data.Typeable

import GHC.Generics.Instances

import Test.QuickCheck
import Test.QuickCheck.Regression
import Test.QuickCheck.Report
import Test.QuickCheck.ZoomEq

import Text.Printf

import Utilities.Syntactic
import Utilities.Table

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

data EvtDecls = Evt (Table (Maybe EventId) EventDecl)
    deriving (Eq,Ord,Show,Typeable,Generic)
    --         -- in Evt, 'Nothing' stands for a dummy

data EventDecl = EventDecl
    { _scope  :: EvtScope Var
    , _source :: NonEmpty EventId
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

instance ZoomEq TheoryConst where
instance Scope TheoryConst where
    kind _ = "constant"
    rename_events' _ e = [e]

instance ZoomEq TheoryDef where
instance Scope TheoryDef where
    kind _ = "constant"
    rename_events' _ e = [e]

instance ZoomEq MachineDef where
instance Scope MachineDef where
    kind _ = "definition"
    rename_events' _ e = [e]

instance ZoomEq MachineVar where
instance Scope MachineVar where
    merge_scopes' (DelMchVar Nothing s _) (MchVar v Inherited li) = Just $ DelMchVar (Just v) s li
    merge_scopes' (MchVar v Inherited li) (DelMchVar Nothing s _) = Just $ DelMchVar (Just v) s li
    merge_scopes' _ _ = Nothing
    kind (DelMchVar _ _ _)   = "deleted variable"
    kind (MchVar _ _ _)  = "state variable"
    rename_events' _ e = [e]

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
                        -- & declSource %~ declUnion (s0^.declSource)
            (Index (InhDelete Nothing),Index (InhAdd v)) -> 
                    Just $ s0
                        & scope .~ Index (InhDelete (Just v))
                        -- & declSource %~ declUnion (s1^.declSource)
            (Param v,Promoted Nothing) -> Just $ s1 
                        & scope .~ Promoted (Just v)
            (Promoted Nothing,Param v) -> Just $ s0 
                        & scope .~ Promoted (Just v) 
            _ -> Nothing
    rename_events' _ e = [e]

instance PrettyPrintable a => PrettyPrintable (EvtScope a) where
    pretty = show . fmap Pretty

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
        x = Evt (fromList [(Nothing,EventDecl {_scope = Param (Var (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) (Gen (DefSort (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) (InternalName "" (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) "") [] (Gen (Sort (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) (InternalName "" (Name {_backslash = False, _base = 'a' :| "", _primes = 0, _suffix = ""}) "") 0) [])) [])), _source = EventId (Lbl "m") :| [], _eventDeclDeclSource = Local, _eventDeclLineInfo = (LI "file" 0 0)})])
        y = Evt (fromList [(Nothing,EventDecl {_scope = Promoted Nothing, _source = EventId (Lbl "c") :| [], _eventDeclDeclSource = Inherited, _eventDeclLineInfo = (LI "file" 0 0)})])
        z = Evt (fromList [(Nothing,EventDecl {_scope = Index (InhDelete Nothing), _source = EventId (Lbl "c") :| [], _eventDeclDeclSource = Local, _eventDeclLineInfo = (LI "file" 0 10)})])

return []

run_tests :: (PropName -> Property -> IO (a, Result))
          -> IO ([a], Bool)
run_tests = $forAllProperties'

