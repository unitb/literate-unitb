{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell    #-}
module UnitB.Property 
    ( Transient   (..)
    , Constraint  (..)
    , ProgressProp(..)
    , SafetyProp  (..) 
    , PropertySet (..) 
    , PropertySetField (..) 
    , empty_property_set
    , TrHint (..)
    , empty_hint
    , makePropertySet
    , changePropertySet
    , ProgId (..)
    , variant_decreased
    , variant_equals_dummy
    , variant_bounded
    , Variant (..)
    , Direction (..)
    , make_unique )
where

    -- Modules
import Logic.Expr
import Logic.Proof

import Theories.SetTheory

    -- Libraries
import Control.DeepSeq

import Data.Default
import Data.DeriveTH
import Data.Map  as M
import Data.List as L
import Data.Typeable

import Utilities.TableConstr

data Constraint = 
        Co [Var] Expr
    deriving (Eq,Ord,Show)


data TrHint = TrHint (Map String (Type,Expr)) (Maybe Label)
    deriving (Eq,Ord,Show)


empty_hint :: TrHint
empty_hint = TrHint empty Nothing

data Transient = 
        Tr 
            (Map String Var)     -- Free variables
            Expr                 -- Predicate
            [Label]              -- Event, Schedule 
            TrHint               -- Hints for instantiation
            -- (Map String Expr)    -- Index substitution
            -- (Maybe Label)        -- Progress Property for fine schedule
    deriving (Eq,Ord,Show)


data Direction = Up | Down
    deriving (Eq,Show)


data Variant = 
        SetVariant     Var Expr Expr Direction
      | IntegerVariant Var Expr Expr Direction
    deriving (Eq,Show)

data PropertySet = PS
        { _transient    :: Map Label Transient
        , _constraint   :: Map Label Constraint
        , _inv          :: Map Label Expr       -- inv
        , _inv_thm      :: Map Label Expr       -- inv thm
        , _proofs       :: Map Label Proof
        , _progress     :: Map Label ProgressProp
--        , schedule     :: Map Label Schedule
        , _safety       :: Map Label SafetyProp
        }
    deriving Eq

newtype ProgId = PId { getProgId :: Label }
    deriving (Eq,Ord)

data ProgressProp = LeadsTo [Var] Expr Expr
    deriving (Eq,Ord,Typeable)

data SafetyProp = Unless [Var] Expr Expr (Maybe Label)
    deriving (Eq,Ord,Typeable)

instance Show ProgressProp where
    show (LeadsTo _ p q) = show p ++ "  |->  " ++ show q

instance Show SafetyProp where
    show (Unless _ p q ev) = show p ++ "  UNLESS  " ++ show q ++ except
        where
            except = maybe "" (("  EXCEPT  " ++) . show) ev

instance Show PropertySet where
    show x = intercalate ", " $ L.map (\(x,y) -> x ++ " = " ++ y)
        [ ("transient",  show $ _transient x)
        , ("constraint", show $ _constraint x)
        , ("inv", show $ _inv x)
        , ("inv_thm", show $ _inv_thm x)
        , ("proofs", show $ keys $ _proofs x)
        , ("progress", show $ _progress x)
        , ("safety", show $ _safety x)
        ]

makeRecordConstr ''PropertySet

empty_property_set :: PropertySet
empty_property_set = makePropertySet []

instance Default PropertySet where
    def = empty_property_set

variant_equals_dummy :: Variant -> Expr
--variant_equals_dummy (SetVariant d var _ _)     = Word d `zeq` var
variant_equals_dummy (IntegerVariant d var _ _) = Word d `zeq` var
variant_equals_dummy (SetVariant d var _ _) = Word d `zeq` var

variant_decreased :: Variant -> Expr
variant_decreased (SetVariant d var _ Up)       = ($fromJust) $ Right (Word d) `zsubset` Right var
variant_decreased (IntegerVariant d var _ Up)   = Word d `zless` var
variant_decreased (SetVariant d var _ Down)     = ($fromJust) $ Right var `zsubset` Right (Word d)
variant_decreased (IntegerVariant d var _ Down) = var `zless` Word d

variant_bounded :: Variant -> Expr
--variant_bounded (SetVariant d var _ _)     = error "set variants unavailable"
variant_bounded (IntegerVariant _ var b Down) = b `zle` var
variant_bounded (IntegerVariant _ var b Up)   = var `zle` b
variant_bounded (SetVariant _ var b Down) = ($fromJust) $ 
    mzand (Right b `zsubset` Right var)
          (mzfinite $ Right var `zsetdiff` Right b)
variant_bounded (SetVariant _ var b Up)   = ($fromJust) $ 
    mzand (Right var `zsubset` Right b)
          (mzfinite $ Right b `zsetdiff` Right var)

make_unique :: String           -- suffix to be added to the name of variables
            -> Map String Var   -- set of variables that must renamed
            -> Expr             -- expression to rewrite
            -> Expr
make_unique suf vs w@(Word (Var vn vt)) 
        | vn `M.member` vs    = Word (Var (vn ++ suf) vt)
        | otherwise           = w
make_unique _ _ c@(Const _ _)    = c
make_unique suf vs (FunApp f xs)     = FunApp f $ L.map (make_unique suf vs) xs
make_unique suf vs (Cast e t)        = Cast (make_unique suf vs e) t
make_unique suf vs (Lift e t)        = Lift (make_unique suf vs e) t
make_unique suf vs (Binder q d r xp t) = Binder q d (f r) (f xp) t
    where
        local = (L.foldr M.delete vs (L.map name d))
        f = make_unique suf local

derive makeNFData ''Constraint
derive makeNFData ''Direction
derive makeNFData ''ProgressProp
derive makeNFData ''PropertySet
derive makeNFData ''SafetyProp
derive makeNFData ''Transient
derive makeNFData ''TrHint
derive makeNFData ''Variant
