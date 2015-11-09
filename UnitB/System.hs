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
import Control.Exception
import Control.Lens hiding (indices)

import           Data.Default
import           Data.Map as M

import Text.Printf

import Utilities.BipartiteGraph
import Utilities.Instances
import Utilities.Invariant

type System = Checked System'

data System' = Sys 
        {  _proof_struct :: [(Label,Label)]
        ,  _ref_struct   :: Map MachineId (Maybe MachineId)
        ,  _machines     :: Map MachineId Machine
        ,  _theories     :: Map String Theory
        }
    deriving (Eq,Generic,Show)

makeLenses ''System'

instance NFData System' where

instance HasInvariant System' where
    invariant s = do 
        "inv4" ## M.keys (s^.ref_struct) === M.keys (s^.machines)
        traverseWithKey (mch match) $ s^.ref_struct
        return ()
        where
            mch cmd m0 m1 = 
                            withPrefix (printf "%s -> %s" (show m0) (show m1)) $
                            -- <$> 
                            cmd ((s^.machines) ! m0) (maybe (empty_machine "empty") ((s^.machines) !) m1)
            match m0 m1   = do
                            "inv0" ## ((m0!.abs_vars) === (m1!.variables))
                                -- del vars is cummulative
                            "inv1" ## ((m0!.del_vars) === (m1!.del_vars) `M.union` ((m0!.abs_vars) `M.difference` (m0!.variables)))
                            "inv2" ## ((m0!.events.to (M.map (view old) . leftMap)) === (m1!.events.to (M.map (view new) . rightMap)))
                            "inv3" ## (m0!.inh_props) === (m1!.inh_props) `mappend` (m1!.props)
                            

instance Controls System' System' where

instance Default System' where
    def = Sys [] M.empty 
        M.empty $ M.fromList 
            [ ("sets",set_theory)
            , ("functions",function_theory)
            , ("arithmetic",arithmetic)
            , ("basic",basic_theory)]

instance Default System where
    def = empty_system

empty_system :: System
empty_system = check assert def
