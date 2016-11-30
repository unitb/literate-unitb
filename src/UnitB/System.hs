{-# LANGUAGE UndecidableInstances,CPP #-} 
module UnitB.System where

    -- Modules
import Logic.Expr.Scope
import Logic.Theory as Th

import Logic.Theories.SetTheory
import Logic.Theories.FunctionTheory
import Logic.Theories.Arithmetic

import UnitB.Event
import UnitB.Expr hiding (merge,target)
import UnitB.Machine 

    -- Libraries
import Control.DeepSeq
import Control.Invariant
import Control.Lens hiding (indices)
import Control.Precondition

import Data.Default
#if MIN_VERSION_transformers(0,5,0)
import Prelude.Extras hiding (Lift1)
#else
import Data.Functor.Classes
#endif
import Data.Functor.Compose
import Data.Graph.Bipartite
import Data.Map as M hiding ((!))
import Data.Serialize

import GHC.Generics.Instances

import Test.QuickCheck.ZoomEq

import Text.Printf

type SystemAST = System' MachineAST
type System' = Compose Checked SystemBase

data SystemBase mch = Sys 
        {  _proof_struct :: [(Label,Label)]
        ,  _ref_struct   :: Map MachineId (Maybe MachineId)
        ,  _machines     :: Map MachineId mch
        ,  _theories     :: Map String Theory
        }
    deriving (Eq,Generic,Show,Functor,Foldable,Traversable)

makeLenses ''SystemBase

instance NFData mch => NFData (SystemBase mch) where

instance (Show mch,HasMachine mch expr,HasExpr expr,ZoomEq expr) 
        => HasInvariant (SystemBase mch) where
    invariant s = do 
        "inv4" ## M.keys (s^.ref_struct) === M.keys (s^.machines)
        _ <- traverseWithKey (mch match) $ s^.ref_struct
        return ()
        where
            mch cmd m0 m1 = 
                            withPrefix (printf "%s -> %s" (show m0) (show m1)) $
                            -- <$> 
                            cmd ((s^.machines) ! m0) (maybe (empty_machine $ fromString'' "empty") ((s^.machines) !) m1)
            match m0 m1   = do
                            "inv0" ## ((m0!.abs_vars) === (m1!.variables))
                                -- del vars is cummulative
                            "inv1" ## ((m0!.del_vars) .== (m1!.del_vars) `M.union` ((m0!.abs_vars) `M.difference` (m0!.variables)))
                            "inv2" ## (M.mapKeys Pretty (m0!.events.to (M.map (view old) . leftMap)) .== M.mapKeys Pretty (m1!.events.to (M.map (view new) . rightMap)))
                            "inv3" ## (m0!.inh_props) === (m1!.inh_props) `mappend` (m1!.props)
                            
instance Controls (SystemBase mch) (SystemBase mch) where

instance Eq1 SystemBase where
#if MIN_VERSION_transformers(0,5,0)
    (==#) = (==)
#else
    eq1 = (==)
#endif

instance Show1 SystemBase where
#if MIN_VERSION_transformers(0,5,0)
#else
    showsPrec1 = showsPrec
#endif

instance Default (SystemBase mch) where
    def = Sys [] M.empty 
        M.empty $ M.fromList 
            [ ("sets",set_theory)
            , ("functions",function_theory)
            , ("arithmetic",arithmetic)
            , ("basic",basic_theory)]

instance (HasMachine mch expr,Show mch,ZoomEq expr) => Default (System' mch) where
    def = empty_system

empty_system :: (HasExpr expr,HasMachine mch expr,Show mch,ZoomEq expr) 
             => System' mch
empty_system = check def

instance Serialize m => Serialize (SystemBase m) where
