{-# LANGUAGE UndecidableInstances #-} 
module UnitB.System where

    -- Modules
import Logic.Expr.Scope
import Logic.Theory as Th

import Theories.SetTheory
import Theories.FunctionTheory
import Theories.Arithmetic

import UnitB.Event
import UnitB.Expr hiding (merge,target)
import UnitB.Machine 

    -- Libraries
import Control.DeepSeq
import Control.Lens hiding (indices)

import           Data.Default
import           Data.Functor.Classes
import           Data.Functor.Compose
import           Data.Graph.Bipartite

import Text.Printf

import Utilities.Instances
import Utilities.Invariant
import Utilities.Map as M hiding ((!))
import Utilities.Partial
import Utilities.Table

type System  = System' Machine
type System' = Compose Checked SystemBase

data SystemBase mch = Sys 
        {  _proof_struct :: [(Label,Label)]
        ,  _ref_struct   :: Table MachineId (Maybe MachineId)
        ,  _machines     :: Table MachineId mch
        ,  _theories     :: Table String Theory
        }
    deriving (Eq,Generic,Show,Functor,Foldable,Traversable)

makeLenses ''SystemBase

instance NFData mch => NFData (SystemBase mch) where

instance (Show mch,HasMachine mch expr,HasExpr expr) 
        => HasInvariant (SystemBase mch) where
    invariant s = do 
        "inv4" ## M.keys (s^.ref_struct) === M.keys (s^.machines)
        traverseWithKey (mch match) $ s^.ref_struct
        return ()
        where
            mch cmd m0 m1 = 
                            withPrefix (printf "%s -> %s" (show m0) (show m1)) $
                            -- <$> 
                            cmd ((s^.machines) ! m0) (maybe (empty_machine $ fromString'' "empty") ((s^.machines) !) m1)
            match m0 m1   = do
                            "inv0" ## ((m0!.abs_vars) === (m1!.variables))
                                -- del vars is cummulative
                            "inv1" ## ((m0!.del_vars) === (m1!.del_vars) `M.union` ((m0!.abs_vars) `M.difference` (m0!.variables)))
                            "inv2" ## ((m0!.events.to (M.map (view old) . leftMap)) === (m1!.events.to (M.map (view new) . rightMap)))
                            "inv3" ## (m0!.inh_props) === (m1!.inh_props) `mappend` (m1!.props)
                            

instance Controls (SystemBase mch) (SystemBase mch) where

instance Eq1 SystemBase where
    eq1 = (==)

instance Show1 SystemBase where
    showsPrec1 = showsPrec

instance Default (SystemBase mch) where
    def = Sys [] M.empty 
        M.empty $ M.fromList 
            [ ("sets",set_theory)
            , ("functions",function_theory)
            , ("arithmetic",arithmetic)
            , ("basic",basic_theory)]

instance (HasMachine mch expr,Show mch) => Default (System' mch) where
    def = empty_system

empty_system :: (HasExpr expr,HasMachine mch expr,Show mch) 
             => System' mch
empty_system = check assert def
