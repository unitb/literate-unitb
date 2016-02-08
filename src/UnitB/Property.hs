module UnitB.Property where

    -- Modules
import Logic.Expr.Scope
import Logic.Proof

import Theories.SetTheory

import UnitB.Expr

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (Const,elements)

import Data.Default
import Data.Foldable
import Data.Hashable
import Data.Semigroup
import Data.List as L
import Data.List.NonEmpty as NE hiding (take)
import Data.String
import Data.Typeable

import GHC.Generics

import Text.Printf

import Test.QuickCheck hiding (label)

import Utilities.Instances
import Utilities.Invariant
import Utilities.Map  as M
import Utilities.Table
import Utilities.TableConstr

type Constraint = Constraint' Expr
type RawConstraint = Constraint' RawExpr

data Constraint' expr = 
        Co [Var] expr
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

type TrHint = TrHint' Expr
type RawTrHint = TrHint' RawExpr

data TrHint' expr = TrHint (Table Name (Type,expr)) (Maybe ProgId)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)


empty_hint :: TrHint' expr
empty_hint = TrHint empty Nothing

type Transient = Transient' Expr
type RawTransient = Transient' RawExpr

data Transient' expr = 
        Tr 
            (Table Name Var)     -- Free variables
            expr                 -- Predicate
            (NonEmpty EventId)   -- Event, Schedule 
            (TrHint' expr)       -- Hints for instantiation
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

data Direction = Up | Down
    deriving (Eq,Show,Generic)

newtype EventId = EventId Label
    deriving (Eq,Ord,Typeable,Generic,Hashable,PrettyPrintable)

instance Arbitrary EventId where
    arbitrary = EventId . label <$> elements ((:[]) <$> take 13 ['a' ..])

instance Show EventId where
    show (EventId x) = show x

instance IsString EventId where
    fromString = EventId . fromString

instance IsLabel EventId where
    as_label (EventId lbl) = lbl

instance PrettyPrintable expr => PrettyPrintable (Transient' expr) where
    pretty (Tr _ expr es hint) = printf "TRANSIENT  %s {%s} [%s]" 
            (pretty expr)
            (pretty $ NE.toList es)
            (pretty hint)

instance PrettyPrintable expr => PrettyPrintable (TrHint' expr) where
    pretty (TrHint subst prog) = printf "HINT: %s %s"
            (reifyPrettyPrint asgn $ \pp -> pretty $ L.map pp $ M.toList subst)
            (show $ Pretty <$> prog)
        where
            asgn (n,(t,e)) = printf "%s := %s (type: %s)" (pretty n) (pretty e) (pretty t)

data Variant = 
        SetVariant     Var RawExpr RawExpr Direction
      | IntegerVariant Var RawExpr RawExpr Direction
    deriving (Eq,Show,Generic)

type PropertySet = PropertySet' Expr
type RawPropertySet = PropertySet' RawExpr

data PropertySet' expr = PS
        { _transient    :: Table Label (Transient' expr)
        , _constraint   :: Table Label (Constraint' expr)
        , _inv          :: Table Label expr       -- inv
        , _inv_thm      :: Table Label expr       -- inv thm
        , _progress     :: Table ProgId (ProgressProp' expr)
        , _safety       :: Table Label (SafetyProp' expr)
        }
    deriving (Eq,Functor,Foldable,Traversable,Generic,Show)

newtype ProgId = PId { getProgId :: Label }
    deriving (Eq,Ord,IsString,Typeable,Generic,Hashable)

instance IsLabel ProgId where
    as_label (PId lbl) = lbl

instance Show ProgId where
    show (PId x) = show x

instance PrettyPrintable ProgId where
    pretty = show

type ProgressProp = ProgressProp' Expr
type RawProgressProp = ProgressProp' RawExpr

data ProgressProp' expr = LeadsTo [Var] expr expr
    deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable,Generic,Show)

type SafetyProp = SafetyProp' Expr
type RawSafetyProp = SafetyProp' RawExpr

data SafetyProp' expr = Unless [Var] expr expr
    deriving (Eq,Ord,Typeable,Functor,Foldable,Traversable,Generic,Show)

instance PrettyPrintable expr => PrettyPrintable (ProgressProp' expr) where
    pretty (LeadsTo _ p q) = pretty p ++ "  |->  " ++ pretty q

instance PrettyPrintable expr => PrettyPrintable (SafetyProp' expr) where
    pretty (Unless _ p q) = pretty p ++ "  UNLESS  " ++ pretty q

instance PrettyPrintable expr => PrettyPrintable (PropertySet' expr) where
    pretty x' = printf "PropertySet { %s }" 
        $ intercalate ", " $ L.map (\(x,y) -> x ++ " = " ++ y)
            [ ("transient",  show $ _transient x)
            , ("constraint", show $ _constraint x)
            , ("inv", show $ _inv x)
            , ("inv_thm", show $ _inv_thm x)
            , ("progress", show $ _progress x)
            , ("safety", show $ _safety x)
            ]
        where
            x = Pretty <$> x'

makeRecordConstr ''PropertySet'

class ReferencesEvents a where
    traverseEvents :: Traversal' a EventId

instance ReferencesEvents (Transient' expr) where
    traverseEvents f (Tr fv p es hint) = Tr fv p <$> traverse f es <*> pure hint

class ReferencesProgress a where
    traverseProgId :: Traversal' a ProgId

instance ReferencesProgress (TrHint' expr) where
    traverseProgId f (TrHint ws p) = TrHint ws <$> traverse f p

instance ReferencesProgress (Transient' expr) where
    traverseProgId f (Tr x y z hint) = Tr x y z <$> traverseProgId f hint

type PropertySetField = PropertySet'Field Expr

empty_property_set :: PropertySet' expr
empty_property_set = makePropertySet' []

instance Default (PropertySet' expr) where
    def = empty_property_set

hasClashes :: PropertySet' expr -> PropertySet' expr -> PropertySet' expr
hasClashes x y = getIntersection $ Intersection x <> Intersection y

noClashes :: (Show expr) => PropertySet' expr -> PropertySet' expr -> Invariant ()
noClashes p0 p1 = allTables inv (hasClashes p0 p1) >> return ()
    where
        inv msg m = withPrefix msg $ do
            (show $ keys m) ## M.null m
            return m

instance Semigroup (Intersection (PropertySet' expr)) where
    (<>) = genericSemigroupMAppendWith

variant_equals_dummy :: Variant -> RawExpr
variant_equals_dummy (IntegerVariant d var _ _) = Word d `zeq` asExpr var
variant_equals_dummy (SetVariant d var _ _) = Word d `zeq` asExpr var

variant_decreased :: Variant -> RawExpr
variant_decreased (SetVariant d var _ Up)       = ($typeCheck) $ Right (Word d) `zsubset` Right (asExpr var)
variant_decreased (IntegerVariant d var _ Up)   = Word d `zless` asExpr var
variant_decreased (SetVariant d var _ Down)     = ($typeCheck) $ Right (asExpr var) `zsubset` Right (Word d)
variant_decreased (IntegerVariant d var _ Down) = asExpr var `zless` Word d

variant_bounded :: Variant -> RawExpr
--variant_bounded (SetVariant d var _ _)     = error "set variants unavailable"
variant_bounded (IntegerVariant _ var b Down) = asExpr b `zle` asExpr var
variant_bounded (IntegerVariant _ var b Up)   = asExpr var `zle` asExpr b
variant_bounded (SetVariant _ var b Down) = ($typeCheck) $ 
    mzand (Right (asExpr b) `zsubset` Right (asExpr var))
          (mzfinite $ Right (asExpr var) `zsetdiff` Right (asExpr b))
variant_bounded (SetVariant _ var b Up)   = ($typeCheck) $ 
    mzand (Right (asExpr var) `zsubset` Right (asExpr b))
          (mzfinite $ Right (asExpr b) `zsetdiff` Right (asExpr var))

makeLenses ''PropertySet'

instance HasScope expr => HasScope (Transient' expr) where
    scopeCorrect' (Tr vs e _ _) = withVars vs $ scopeCorrect' e

instance HasScope expr => HasScope (ProgressProp' expr) where
    scopeCorrect' (LeadsTo vs p q) = withVars vs $ scopeCorrect' p <> scopeCorrect' q

instance HasScope expr => HasScope (SafetyProp' expr) where
    scopeCorrect' (Unless vs p q) = withVars vs $ scopeCorrect' p <> scopeCorrect' q

instance HasScope expr => HasScope (Constraint' expr) where
    scopeCorrect' (Co vs e) = withPrimes $ withVars vs $ scopeCorrect' e

--instance HasScope Proof where
--    scopeCorrect' (Easy _) = return []
--    scopeCorrect' (FreeGoal _ u t p _) = withVars [Var u t] $ scopeCorrect' p
--    scopeCorrect' (ByCases xs _) = fold $ L.map (scopeCorrect'.view _3) xs <> L.map (scopeCorrect'.view _2) xs
--    scopeCorrect' (ByParts xs _) = fold $ L.map (scopeCorrect'.view _1) xs <> L.map (scopeCorrect'.view _2) xs
--    scopeCorrect' (Assume xs goal p _) = _
--    scopeCorrect' (Assertion _ _ _ _) = _
--    scopeCorrect' (Definition _ _ _) = _
--    scopeCorrect' (InstantiateHyp _ _ _ _) = _
--    scopeCorrect' (Keep _ _ _ _ _) = _
--    scopeCorrect' (ByCalc _) = _

instance HasScope expr => HasScope (PropertySet' expr) where
    scopeCorrect' x = withPrefix "props" $ fold $
        [ withPrefix "transient"  $ foldMapWithKey scopeCorrect'' (x^.transient)
        , withPrefix "constraint" $ foldMapWithKey scopeCorrect'' (x^.constraint)
        , withPrefix "invariant"  $ foldMapWithKey scopeCorrect'' (x^.inv)
        , withPrefix "theorem"    $ foldMapWithKey scopeCorrect'' (x^.inv_thm)
        , withPrefix "progress"   $ foldMapWithKey scopeCorrect'' (x^.progress)
        , withPrefix "safety" $ foldMapWithKey scopeCorrect'' (x^.safety)
        --, withPrefix "proofs" $ foldMapWithKey scopeCorrect'' (x^.proofs)
        ]

instance Monoid (PropertySet' expr) where
    mempty  = genericMEmpty
    mappend = genericMAppend
    mconcat = genericMConcat

instance Arbitrary expr => Arbitrary (ProgressProp' expr) where
    arbitrary = genericArbitrary
instance Arbitrary expr => Arbitrary (SafetyProp' expr) where
    arbitrary = genericArbitrary
instance Arbitrary expr => Arbitrary (Constraint' expr) where
    arbitrary = genericArbitrary
instance Arbitrary expr => Arbitrary (Transient' expr) where
    arbitrary = Tr <$> (M.fromList <$> arbitrary) 
                   <*> arbitrary 
                   <*> (NE.nub <$> arbitrary) 
                   <*> arbitrary
instance Arbitrary ProgId where
    arbitrary = genericArbitrary
instance Arbitrary expr => Arbitrary (TrHint' expr) where
    arbitrary = TrHint <$> (M.fromList <$> arbitrary) <*> arbitrary

instance NFData ProgId
instance NFData expr => NFData (Constraint' expr)
instance NFData Direction
instance NFData expr => NFData (ProgressProp' expr)
instance NFData expr => NFData (PropertySet' expr)
instance NFData expr => NFData (SafetyProp' expr)
instance NFData expr => NFData (Transient' expr)
instance NFData expr => NFData (TrHint' expr)
instance NFData Variant
instance NFData EventId