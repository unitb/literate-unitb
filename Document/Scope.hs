module Document.Scope where

    -- Modules
import Logic.Expr

import UnitB.AST

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Monad

import Data.Map as M

import Utilities.Format
import Utilities.Syntactic

    -- clashes is a symmetric, reflexive relation
class Ord a => Scope a where
    make_inherited :: a -> Maybe a
    keep_from :: DeclSource -> a -> Maybe a
    error_item :: a -> (String,LineInfo)
    clashes :: a -> a -> Bool
    merge_scopes :: a -> a -> a

is_inherited :: Scope s => s -> Maybe s
is_inherited = keep_from Inherited

is_local :: Scope s => s -> Maybe s
is_local = keep_from Local

instance Scope VarScope where
    keep_from s (Evt m) = Just $ Evt $ M.mapMaybe f m
        where
            f x@(_,_,s',_)
                | s == s'   = Just x
                | otherwise = Nothing
    keep_from s x
            | f x == s  = Just x
            | otherwise = Nothing
        where
            f (TheoryDef _ s _) = s
            f (TheoryConst _ s _) = s
            f (Machine _ s _) = s
            f (DelMch _ s _) = s
            f (Evt _) = error "is_inherited Scope VarScope"
    make_inherited (TheoryDef x _ y) = Just $ TheoryDef x Inherited y
    make_inherited (TheoryConst x _ y) = Just $ TheoryConst x Inherited y
    make_inherited (Machine x _ y) = Just $ Machine x Inherited y
    make_inherited (DelMch x _ y)  = Just $ DelMch x Inherited y
    make_inherited (Evt m) = Just $ Evt $ M.map f m
        where
            f (x,y,_,z) = (x,y,Inherited,z)
    clashes (Evt m0) (Evt m1) = not $ M.null $ m0 `M.intersection` m1
    clashes (DelMch _ _ _) (Machine _ Inherited _) = False
    clashes (Machine _ Inherited _) (DelMch _ _ _) = False
    clashes _ _ = True
    error_item (Evt m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' _ = error "VarScope Scope VarScope: head'"
            msg (Just k) (_v,sc,_,li) = (format "{1} (event {0})" k sc :: String, li)
            msg Nothing (_v,_,_,li) = (format "dummy", li)
    error_item (Machine _ _ li)   = ("state variable", li)
    error_item (TheoryDef _ _ li) = ("constant", li)
    error_item (TheoryConst _ _ li) = ("constant", li)
    error_item (DelMch _ _ li)   = ("deleted variable", li)
    merge_scopes (Evt m0) (Evt m1) = Evt $ unionWith (error "VarScope Scope.merge_scopes: Evt, Evt") m0 m1
    merge_scopes (DelMch _ s _) (Machine v Inherited li) = DelMch (Just v) s li
    merge_scopes (Machine v Inherited li) (DelMch _ s _) = DelMch (Just v) s li
    merge_scopes _ _ = error "VarScope Scope.merge_scopes: _, _"

data VarScope =
        TheoryConst Var DeclSource LineInfo
        | TheoryDef Def DeclSource LineInfo
        | Machine Var DeclSource LineInfo
        | DelMch (Maybe Var) DeclSource LineInfo
        | Evt (Map (Maybe EventId) (Var,EvtScope,DeclSource,LineInfo))
            -- in Evt, 'Nothing' stands for a dummy
    deriving (Eq,Ord,Show)

-- instance NFData VarScope where

data EvtScope = Param | Index
    deriving (Eq,Ord)

data DeclSource = Inherited | Local
    deriving (Eq,Ord,Show)

data EvtExprScope = 
        CoarseSchedule Expr
        | FineSchedule Expr
        | Guard Expr
        | Witness Var Expr
        | DelAction (Maybe Action)
        | Action Action
    deriving (Eq,Ord)

instance Show EvtExprScope where
    show (CoarseSchedule _) = "coarse schedule"
    show (FineSchedule _) = "fine schedule"
    show (Witness _ _) = "witness"
    show (Guard _) = "guard"
    show (Action _) = "action"
    show (DelAction _) = "delete action"

data ExprScope = 
        EventExpr (Map (Maybe EventId) (EvtExprScope,DeclSource,LineInfo))
        | Invariant Expr DeclSource LineInfo
        | TransientProp Transient DeclSource LineInfo
        | ConstraintProp Constraint DeclSource LineInfo
        | SafetyProp SafetyProp DeclSource LineInfo
        | ProgressProp ProgressProp DeclSource LineInfo
        | Initially Expr DeclSource LineInfo
        | DelInit (Maybe Expr) DeclSource LineInfo
        | Axiom Expr DeclSource LineInfo
    deriving (Eq,Ord)

-- instance NFData ExprScope where

instance Show EvtScope where
    show Param = "parameter"
    show Index = "index"

instance Scope ExprScope where
    keep_from s (EventExpr m) = Just $ EventExpr $ M.mapMaybe f m
        where
            f x@(DelAction _,_,_) 
                | s == Inherited = Just x
            f x@(_,s',_)
                | s == s'   = Just x
                | otherwise = Nothing
    keep_from s x
            | f x == s  = Just x
            | otherwise = Nothing
        where
            f (Invariant _ s _) = s
            f (TransientProp _ s _) = s
            f (ConstraintProp _ s _) = s
            f (SafetyProp _ s _) = s
            f (ProgressProp _ s _) = s
            f (Initially _ s _) = s
            f (DelInit _ _ _) = Inherited
            f (Axiom _ s _) = s
            f (EventExpr _) = error "is_inherited Scope VarScope"
    make_inherited (Invariant x _ y) = Just $ Invariant x Inherited y
    make_inherited (TransientProp x _ y) = Just $ TransientProp x Inherited y
    make_inherited (ConstraintProp x _ y) = Just $ ConstraintProp x Inherited y
    make_inherited (SafetyProp x _ y) = Just $ SafetyProp x Inherited y
    make_inherited (ProgressProp x _ y) = Just $ ProgressProp x Inherited y
    make_inherited (Initially x _ y) = Just $ Initially x Inherited y
    make_inherited (DelInit x _ y) = Just $ DelInit x Inherited y
    make_inherited (Axiom x _ y) = Just $ Axiom x Inherited y
    make_inherited (EventExpr m) = EventExpr <$> g (M.mapMaybe f m)
        where
            g x = guard (not $ M.null x) >> return x
            f (x,_,z) = Just (x,Inherited,z)
    clashes (EventExpr m0) (EventExpr m1) = not $ M.null 
            $ M.filter (uncurry (==))
            $ M.intersectionWith (curry $ is_del *** is_del) m0 m1
        where
            is_del (x,_,_) = case x of DelAction _ -> True ; _ -> False 
    clashes (DelInit _ _ _) (Initially _ _ _) = False
    clashes (Initially _ _ _) (DelInit _ _ _) = False
    clashes _ _ = True
    error_item (EventExpr m) = head' $ elems $ mapWithKey msg m
        where
            head' [x] = x
            head' _ = error "Scope ExprScope: head'"
            msg (Just k) (sc,_,li) = (format "{1} (event {0})" k sc :: String, li)
            msg Nothing (sc,_,li) = (format "{0} (initialization)" sc :: String, li)
    error_item (Invariant _ _ li)   = ("invariant", li)
    error_item (TransientProp _ _ li) = ("transient predicate", li)
    error_item (ConstraintProp _ _ li) = ("co property", li)
    error_item (SafetyProp _ _ li) = ("safety property", li)
    error_item (ProgressProp _ _ li) = ("progress property", li)
    error_item (Initially _ _ li) = ("initialization", li)
    error_item (DelInit _ _ li) = ("delete initialization", li)
    error_item (Axiom _ _ li) = ("assumtion", li)
    merge_scopes (EventExpr m0) (EventExpr m1) = EventExpr $ unionWith f m0 m1
        where
            f (DelAction _,y,li) (Action a,_,_) = (DelAction (Just a),y,li)
            f (Action a,_,_) (DelAction _,y,li) = (DelAction (Just a),y,li)
            f _ _ = (error "ExprScope Scope.merge_scopes: Evt, Evt")
    merge_scopes (DelInit _ s li) (Initially e _ _) = DelInit (Just e) s li
    merge_scopes (Initially e _ _) (DelInit _ s li) = DelInit (Just e) s li
    merge_scopes _ _ = error "ExprScope Scope.merge_scopes: _, _"
