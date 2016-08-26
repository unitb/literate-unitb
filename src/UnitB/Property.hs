{-# LANGUAGE ExistentialQuantification
        ,StandaloneDeriving
        ,TypeOperators #-}
module UnitB.Property where

    -- Modules
import Logic.Expr.Scope
import Logic.Proof

import Logic.Theories.SetTheory

import UnitB.Expr hiding (Lifting)
import UnitB.Expr.Scope

    -- Libraries
import           Bound hiding (Var)
import           Bound.Var hiding (Var)
import           Bound.Scope
import qualified Bound as B 

import Control.DeepSeq
import Control.Invariant
import Control.Lens hiding (Const,elements)

import Data.Bifoldable
import Data.Bytes.Serial
import Data.Constraint
import Data.Constraint.Forall
import Data.Constraint.Lifting
import Data.Default
import Data.Foldable
import Data.Hashable
import Data.List as L
import Data.List.NonEmpty as NE hiding (take)
import Data.MakeTable
import Data.Map.Class  as M
import Data.Monoid as M
import Data.Semigroup as S
import Data.Serialize hiding (label)
import Data.String
import Data.Type.Map hiding (Table)
import qualified Data.Type.Map as TM
import Data.Typeable

import GHC.Generics
import GHC.Generics.Instances

import Prelude.Extras

import Text.Printf

import Test.QuickCheck as QC hiding (label)
import Test.QuickCheck.ZoomEq

import Utilities.Table

type Constraint = Constraint' Expr
type RawConstraint = Constraint' RawExpr

newtype ConstraintIntl expr lv v = Co (Scope lv expr v)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

newtype Constraint' expr v = CP (Scoped (ConstraintIntl expr) Var v)
    deriving (Eq,Ord,Functor,Foldable,Traversable,Generic)

instance Show (Constraint' expr v) where

instance Functor expr => Bifunctor (ConstraintIntl expr) where
    bimap f g (Co p) = Co $ mapScope f g p
instance Foldable expr => Bifoldable (ConstraintIntl expr) where
    bifoldMap f g (Co p) = foldMapScope f g p

-- deriving instance Functor expr => Functor     (Constraint' expr)
-- deriving instance Foldable expr => Foldable    (Constraint' expr)
-- deriving instance Traversable expr => Traversable (Constraint' expr)

type TrHint = TrHint' Expr
type RawTrHint = TrHint' RawExpr

data TrHint' expr v = TrHint (Table Name (Type,expr v)) (Maybe ProgId)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Generic)


empty_hint :: TrHint' expr v
empty_hint = TrHint empty Nothing

type Transient = Transient' Expr
type RawTransient = Transient' RawExpr

data TransientIntl expr lv v = 
        Tr
            (Scope lv expr v)    -- Predicate
            (NonEmpty EventId)   -- Event, Schedule 
            (TrHint' expr v)     -- Hints for instantiation
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Typeable,Generic)

newtype Transient' expr v = 
        T (Scoped (TransientIntl expr) Var v)
    deriving (Eq,Ord,Functor,Foldable,Traversable,Typeable,Generic)

instance Show (Transient' expr v) where

instance Functor expr => Bifunctor (TransientIntl expr) where
    bimap f g (Tr p x y) = Tr (mapScope f g p) x (g <$> y)
instance Foldable expr => Bifoldable (TransientIntl expr) where
    bifoldMap f g (Tr p x y) = foldMapScope f g p M.<> foldMap g y

-- deriving instance Functor expr => Functor     (Transient' expr)
-- deriving instance Foldable expr => Foldable    (Transient' expr)
-- deriving instance Traversable expr => Traversable (Transient' expr)

data Direction = Up | Down
    deriving (Eq,Show,Generic)

newtype EventId = EventId Label
    deriving (Eq,Show,Ord,Typeable,Generic,Hashable,PrettyPrintable)

instance ZoomEq EventId where
    (.==) = (QC.===)
instance Arbitrary EventId where
    arbitrary = EventId . label <$> elements ((:[]) <$> take 13 ['a' ..])
    shrink = genericShrink

instance IsString EventId where
    fromString = EventId . fromString

instance IsLabel EventId where
    as_label (EventId lbl) = lbl

instance (PrettyPrintable (expr Name),Monad expr) 
        => PrettyPrintable (TransientIntl expr Var Name) where
    pretty (Tr expr es hint) = 
        printf "TRANSIENT  %s {%s} [%s]" 
            (pretty $ B.instantiate (pure . view name) expr)
            (pretty $ NE.toList es)
            (pretty hint)

-- instance (PrettyPrintable (expr Name),Monad expr) 
--         => PrettyPrintable (Transient' expr Name) where
--     pretty (T t) = pretty t

newtype IndexInstance expr = IndexInstance { unIndexInstance :: (Name,(Type,expr)) } 
    deriving (Eq, Show)

instance PrettyPrintable expr => PrettyPrintable (IndexInstance expr) where
    pretty (IndexInstance (n,(t,e))) = printf "%s := %s (type: %s)" (pretty n) (pretty e) (pretty t)

instance PrettyPrintable (expr Name) => PrettyPrintable (TrHint' expr Name) where
    pretty (TrHint subst prog) = printf "HINT: %s %s"
            (pretty $ L.map IndexInstance $ M.toList subst)
            (show $ Pretty <$> prog)

data VariantType = SetVariant | IntegerVariant
    deriving (Eq,Show,Generic)

data Variant v = Variant VariantType Var 
        (RawExpr v) 
        (RawExpr v)
        Direction
    deriving (Eq,Show,Generic)

type PropertySet = PropertySet' Expr
type RawPropertySet = PropertySet' RawExpr

data PropertySet' expr v = PS
        { _transient    :: Table Label (Transient' expr v)
        , _constraint   :: Table Label (Constraint' expr v)
        , _inv          :: Table Label (expr v)
        , _inv_thm      :: Table Label (expr v)
        , _progress     :: Table ProgId (ProgressProp' expr v)
        , _safety       :: Table Label  (SafetyProp' expr v)
        }
    deriving (Eq,Functor,Foldable,Traversable,Generic,Show)

newtype ProgId = PId { getProgId :: Label }
    deriving (Eq,Ord,IsString,Typeable,Generic,Hashable)

instance IsLabel ProgId where
    as_label (PId lbl) = lbl

instance Show ProgId where
    show (PId x) = show x

instance PrettyPrintable ProgId where
    pretty (PId x) = pretty x

type ProgressProp = ProgressProp' Expr
type RawProgressProp = ProgressProp' RawExpr

data ProgressPropIntl expr lv v =           
        LeadsTo (Scope lv expr v) 
                (Scope lv expr v)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Typeable,Generic)

newtype ProgressProp' expr v = 
        PP (Scoped (ProgressPropIntl expr) Var v)
    deriving (Eq,Ord,Functor,Foldable,Traversable,Typeable,Generic)

instance Show (ProgressProp' expr v) where

instance Functor expr => Bifunctor (ProgressPropIntl expr) where
    bimap f g (LeadsTo p q) = LeadsTo (mapScope f g p) (mapScope f g q)
instance Foldable expr => Bifoldable (ProgressPropIntl expr) where
    bifoldMap f g (LeadsTo p q) = foldMapScope f g p M.<> foldMapScope f g q

-- deriving instance Functor expr => Functor     (ProgressProp' expr)
-- deriving instance Foldable expr => Foldable    (ProgressProp' expr)
-- deriving instance Traversable expr => Traversable (ProgressProp' expr)

type SafetyProp = SafetyProp' Expr
type RawSafetyProp = SafetyProp' RawExpr

data SafetyPropIntl expr lv v = 
            Unless (Scope lv expr v) 
                   (Scope lv expr v)
    deriving (Eq,Ord,Show,Functor,Foldable,Traversable,Typeable,Generic)

newtype SafetyProp' expr v = 
        SP (Scoped (SafetyPropIntl expr) Var v)
    deriving (Eq,Ord,Functor,Foldable,Traversable,Typeable,Generic)

instance Show (SafetyProp' expr v) where

instance Functor expr => Bifunctor (SafetyPropIntl expr) where
    bimap f g (Unless p q) = Unless (mapScope f g p) (mapScope f g q)
instance Foldable expr => Bifoldable (SafetyPropIntl expr) where
    bifoldMap f g (Unless p q) = foldMapScope f g p M.<> foldMapScope f g q

-- deriving instance Functor expr => Functor     (SafetyProp' expr)
-- deriving instance Foldable expr => Foldable    (SafetyProp' expr)
-- deriving instance Traversable expr => Traversable (SafetyProp' expr)

instance (PrettyPrintable (expr Name),Monad expr) 
        => PrettyPrintable (ProgressPropIntl expr Var Name) where
    pretty (LeadsTo p q) = pretty (B.instantiate (pure . view name) p) 
                    ++ "  |->  " 
                    ++ pretty (B.instantiate (pure . view name) q)

instance (PrettyPrintable (expr Name),Monad expr) 
        => PrettyPrintable (SafetyPropIntl expr Var Name) where
    pretty (Unless p q) = pretty (B.instantiate (pure . view name) p) 
                    ++ "  UNLESS  "
                    ++ pretty (B.instantiate (pure . view name) q)

instance (PrettyPrintable (expr Name),Functor expr) 
        => PrettyPrintable (PropertySet' expr Name) where
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

instance ReferencesEvents (Transient' expr v) where
    traverseEvents f (T (Scoped t (Tr p es hint))) = 
        T . Scoped t <$> (Tr p <$> traverse f es 
                                           <*> pure hint)

class ReferencesProgress a where
    traverseProgId :: Traversal' a ProgId

instance ReferencesProgress (TrHint' expr v) where
    traverseProgId f (TrHint ws p) = TrHint ws <$> traverse f p

instance ReferencesProgress (Transient' expr v) where
    traverseProgId f (T (Scoped t (Tr y z hint))) = 
        T . Scoped t <$> (Tr y z <$> traverseProgId f hint)

type PropertySetField = PropertySet'Field Expr

empty_property_set :: PropertySet' expr v
empty_property_set = makePropertySet' []

instance Default (PropertySet' expr v) where
    def = empty_property_set

hasClashes :: PropertySet' expr v -> PropertySet' expr v -> PropertySet' expr v
hasClashes x y = getIntersection $ Intersection x S.<> Intersection y

noClashes :: (Show (expr v)) => PropertySet' expr v -> PropertySet' expr v -> Invariant
noClashes p0 p1 = allTables inv (hasClashes p0 p1) >> return ()
    where
        inv msg m = withPrefix msg $ do
            (show $ keys m) ## M.null m
            return m

instance Semigroup (Intersection (PropertySet' expr v)) where
    (<>) = genericSemigroupMAppendWith

variant_equals_dummy :: Variant v -> RawExpr v
variant_equals_dummy (Variant IntegerVariant d var _ _) = Word d `zeq` asExpr var
variant_equals_dummy (Variant SetVariant d var _ _) = Word d `zeq` asExpr var

variant_decreased :: Variant v -> RawExpr v
variant_decreased (Variant SetVariant d var _ Up)       = ($typeCheck) $ Right (Word d) `zsubset` Right (asExpr var)
variant_decreased (Variant IntegerVariant d var _ Up)   = Word d `zless` asExpr var
variant_decreased (Variant SetVariant d var _ Down)     = ($typeCheck) $ Right (asExpr var) `zsubset` Right (Word d)
variant_decreased (Variant IntegerVariant d var _ Down) = asExpr var `zless` Word d

variant_bounded :: Variant v -> RawExpr v
--variant_bounded (SetVariant d var _ _)     = error "set variants unavailable"
variant_bounded (Variant IntegerVariant _ var b Down) = asExpr b `zle` asExpr var
variant_bounded (Variant IntegerVariant _ var b Up)   = asExpr var `zle` asExpr b
variant_bounded (Variant SetVariant _ var b Down) = ($typeCheck) $ 
    mzand (Right (asExpr b) `zsubset` Right (asExpr var))
          (mzfinite $ Right (asExpr var) `zsetdiff` Right (asExpr b))
variant_bounded (Variant SetVariant _ var b Up)   = ($typeCheck) $ 
    mzand (Right (asExpr var) `zsubset` Right (asExpr b))
          (mzfinite $ Right (asExpr b) `zsetdiff` Right (asExpr var))

makeLenses ''PropertySet'

-- instance HasScope (expr v) => HasScope (Transient' expr v) where
--     scopeCorrect' (Tr vs e _ _) = withVars vs $ scopeCorrect' e

-- instance HasScope (expr v) => HasScope (ProgressProp' expr v) where
--     scopeCorrect' (LeadsTo vs p q) = withVars vs $ scopeCorrect' p <> scopeCorrect' q

-- instance HasScope (expr v) => HasScope (SafetyProp' expr v) where
--     scopeCorrect' (Unless vs p q) = withVars vs $ scopeCorrect' p <> scopeCorrect' q

-- instance HasScope (expr v) => HasScope (Constraint' expr v) where
--     scopeCorrect' (Co vs e) = withPrimes $ withVars vs $ scopeCorrect' e

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

-- instance HasScope (expr v) => HasScope (PropertySet' expr v) where
--     scopeCorrect' x = withPrefix "props" $ fold $
--         [ withPrefix "transient"  $ foldMapWithKey scopeCorrect'' (x^.transient)
--         , withPrefix "constraint" $ foldMapWithKey scopeCorrect'' (x^.constraint)
--         , withPrefix "invariant"  $ foldMapWithKey scopeCorrect'' (x^.inv)
--         , withPrefix "theorem"    $ foldMapWithKey scopeCorrect'' (x^.inv_thm)
--         , withPrefix "progress"   $ foldMapWithKey scopeCorrect'' (x^.progress)
--         , withPrefix "safety" $ foldMapWithKey scopeCorrect'' (x^.safety)
--         --, withPrefix "proofs" $ foldMapWithKey scopeCorrect'' (x^.proofs)
--         ]

instance (Eq1 expr,Show1 expr,Monad expr,ZoomEq v,Lifting ZoomEq expr,Eq (expr v),Show (expr v)) 
        => ZoomEq (PropertySet' expr v) where
    (.==) = genericZoomEq' lifting
instance Monoid (PropertySet' expr v) where
    mempty  = genericMEmpty
    mappend = genericMAppend
    mconcat = genericMConcat

genericZoomEq' :: ZoomEq a
               => ZoomEq a :- ZoomEq (f a)
               -> f a -> f a -> Property
genericZoomEq' (Sub Dict) = (.==)

genericZoomEq2' :: (ZoomEq a,ZoomEq b)
                => ZoomEq a :- Lifting ZoomEq (f a)
                -> f a b -> f a b -> Property
genericZoomEq2' (Sub Dict) = genericZoomEq' lifting

instance Lifting ZoomEq (PropertySet' expr) where
instance Lifting ZoomEq (ConstraintIntl expr lv) where
instance Lifting ZoomEq (ProgressPropIntl expr lv) where
instance Lifting ZoomEq (SafetyPropIntl expr lv) where
instance Lifting ZoomEq (TransientIntl expr lv) where

instance (Monad expr,ZoomEq lv,ZoomEq v,Lifting ZoomEq expr,Show1 expr,Eq1 expr,ZoomEq (expr v)) 
        => ZoomEq (TransientIntl expr lv v) where
    (.==) = genericZoomEq' lifting
instance (Monad expr,ZoomEq lv,ZoomEq v,Lifting ZoomEq expr,Show1 expr,Eq1 expr,ZoomEq (expr v)) 
        => ZoomEq (ConstraintIntl expr lv v) where
    (.==) = genericZoomEq' lifting
instance () => Arbitrary (ConstraintIntl expr lv v) where
instance (Monad expr,ZoomEq lv,ZoomEq v,Lifting ZoomEq expr,Show1 expr,Eq1 expr,ZoomEq (expr v)) 
        => ZoomEq (SafetyPropIntl expr lv v) where
    (.==) = genericZoomEq' lifting
instance () => Arbitrary (SafetyPropIntl expr lv v) where
instance (Monad expr,ZoomEq lv,ZoomEq v,Lifting ZoomEq expr,Show1 expr,Eq1 expr,ZoomEq (expr v)) 
        => ZoomEq (ProgressPropIntl expr lv v) where
    (.==) = genericZoomEq' lifting
instance () => Arbitrary (ProgressPropIntl expr lv v) where

instance (Eq1 expr,Show1 expr,Monad expr,ZoomEq v,Lifting ZoomEq expr,ZoomEq (expr v)) 
        => ZoomEq (ProgressProp' expr v) where
instance (Arbitrary (expr v),Functor expr,Foldable expr) => Arbitrary (ProgressProp' expr v) where
    arbitrary = genericArbitrary
instance (Eq1 expr,Show1 expr,Monad expr,ZoomEq v,ZoomEq (expr v),Lifting ZoomEq expr)
        => ZoomEq (SafetyProp' expr v) where
instance (Functor expr,Arbitrary (expr v),Foldable expr) => Arbitrary (SafetyProp' expr v) where
    arbitrary = genericArbitrary
instance (Eq1 expr,Monad expr,ZoomEq v,ZoomEq (expr v),Lifting ZoomEq expr,Show1 expr) 
        => ZoomEq (Constraint' expr v) where
instance (Arbitrary (expr v),Functor expr,Foldable expr) => Arbitrary (Constraint' expr v) where
    arbitrary = genericArbitrary
instance (Eq1 expr,Monad expr,ZoomEq v,ZoomEq (expr v),Lifting ZoomEq expr,Show1 expr) 
        => ZoomEq (Transient' expr v) where
instance (Monad expr,Arbitrary (expr v),Lifting Arbitrary expr,Arbitrary v,Functor expr,Foldable expr) => Arbitrary (Transient' expr v) where
    arbitrary = genericArbitrary
instance (Monad expr,Arbitrary (expr v),Lifting Arbitrary expr,Arbitrary lv,Arbitrary v,Functor expr,Foldable expr) => Arbitrary (TransientIntl expr lv v) where
    arbitrary = Tr <$> arbitrary 
                   <*> (NE.nub <$> arbitrary) 
                   <*> arbitrary
instance ZoomEq ProgId where
    (.==) = (QC.===)
instance Arbitrary ProgId where
    arbitrary = genericArbitrary
instance ZoomEq (expr v) => ZoomEq (TrHint' expr v) where
instance Arbitrary (expr v) => Arbitrary (TrHint' expr v) where
    arbitrary = TrHint <$> (M.fromList <$> arbitrary) <*> arbitrary

instance ZoomEq VariantType where
instance ZoomEq Direction where
instance ZoomEq (Variant v) where

instance NFData ProgId
instance (NFData (expr v),NFData v,Foldable expr) => NFData (Constraint' expr v)
instance NFData Direction
instance (NFData (expr v),NFData v,Foldable expr) => NFData (ProgressProp' expr v)
instance (NFData (expr v),NFData v,Foldable expr) => NFData (PropertySet' expr v)
instance (NFData (expr v),NFData v,Foldable expr) => NFData (SafetyProp' expr v)
instance (NFData (expr v),NFData v,Foldable expr) => NFData (Transient' expr v)
instance NFData (expr v) => NFData (TrHint' expr v)
instance NFData (Variant v)
instance NFData EventId
instance NFData VariantType

instance (Serialize lv,Serialize v,Serial1 expr) => Serialize (SafetyPropIntl expr lv v) where
instance (Serialize lv,Serialize v,Serial1 expr) => Serialize (ProgressPropIntl expr lv v) where
instance (Serialize lv,Serialize v,Serial1 expr) => Serialize (ConstraintIntl expr lv v) where
instance (Serialize lv,Serialize v,Serial1 expr,Serialize (expr v)) => Serialize (TransientIntl expr lv v) where
instance Serialize ProgId where
instance Serialize Direction where
instance Serialize VariantType where
instance Serialize (expr v) => Serialize (TrHint' expr v) where
instance (Foldable expr,Functor expr,Serial1 expr,Serialize (expr v),Serialize v) => Serialize (Transient' expr v) where
instance (Foldable expr,Functor expr,Serial1 expr,Serialize (expr v),Serialize v) => Serialize (SafetyProp' expr v) where
instance (Foldable expr,Functor expr,Serial1 expr,Serialize (expr v),Serialize v) => Serialize (ProgressProp' expr v) where
instance (Foldable expr,Functor expr,Serial1 expr,Serialize (expr v),Serialize v) => Serialize (Constraint' expr v) where
instance (Foldable expr,Functor expr,Serial1 expr,Serialize (expr v),Serialize v) => Serialize (PropertySet' expr v) where
instance Serialize (Variant v) where
instance Serialize EventId where
