{-# LANGUAGE TypeFamilies,StandaloneDeriving,CPP #-}
module UnitB.UnitB 
    ( module UnitB.Syntax
    , module UnitB.UnitB 
    , theory_po )
where

    -- Modules
import UnitB.Expr
import UnitB.PO 
import UnitB.Syntax 

import Logic.Expr.Scope
import Logic.Proof
import Logic.Proof.Tactics hiding (assert)
--import           Logic.Proof.POGenerator hiding ( variables )
--import qualified Logic.Proof.POGenerator as POG
--import Logic.Theory
--import Logic.WellDefinedness

import Z3.Z3

    -- Libraries
import Control.DeepSeq
import Control.Invariant
import Control.Lens  hiding (indices,Context,Context',(.=))
import Control.Lens.Misc
import Control.Monad hiding (guard)
import Control.Precondition

import           Data.Default
import           Data.Compressed
import           Data.Either.Validation
#if MIN_VERSION_transformers(0,5,0)
import Prelude.Extras hiding (Lift1)
import qualified Data.Functor.Classes as F
#else
import Data.Functor.Classes
#endif
import           Data.Functor.Compose
import           Data.List as L hiding (inits, union,insert)
import           Data.Map as M hiding 
                    ( map, (!)
                    , delete, filter, null
                    , (\\), mapMaybe )
import qualified Data.Map as M
import           Data.Serialize
import qualified Data.Set as S

import GHC.Generics (Generic1)
import GHC.Generics.Instances

import Test.QuickCheck.ZoomEq

import Text.Printf.TH as Printf

import Utilities.Syntactic

type Machine' = Compose Checked MachinePO'
type RawMachine = Machine' RawExpr
type Machine = Machine' Expr

type SystemSyntax' expr = SystemBase (MachineWithProofs' expr)
type SystemSyntax  = SystemSyntax' RawExpr
type SystemSemantics' expr = System' (Machine' expr)
type SystemSemantics  = SystemSemantics' RawExpr
type System  = System' Machine
type CompressedSystem  = Compressed (Compose SystemBase MachineWithProofs') RawExpr
type RawSystem = System' (Machine' RawExpr)

type MachineWithProofs = MachineWithProofs' RawExpr

data MachineWithProofs' expr = MachineWithProofs 
                (MachineBase expr) 
                (Map Label (ProofBase expr))
    deriving (Functor,Foldable,Traversable,Generic)

type Key    = (Label,Label)
type SeqMap = Map Key (Sequent,Maybe Bool)

data MachinePO' expr = MachinePO
    { _syntax :: MachineAST' expr 
    , _proofs     :: Map Label Proof    
    , _raw_proof_obligation_field :: Box (Map Label Sequent)
    , _proof_obligation_field :: MemBox (Map Label Sequent) }
    deriving (Functor,Foldable,Traversable,Show,Generic,Generic1,Eq)

newtype Box a = Box (() -> a)
    deriving (Generic)
newtype MemBox a = MemBox a
    deriving (Eq,Default,NFData,Generic)

class IsBox f where
    box :: (() -> a) -> f a
    unbox :: f a -> a

instance IsBox Box where
    unbox (Box f) = f ()
    box = Box

instance IsBox MemBox where
    unbox (MemBox x) = x
    box = MemBox . ($ ())

instance Show a => Show (Box a) where
    show (Box f) = show $ f ()

instance Eq a => Eq (Box a) where
    Box f == Box g = f () == g ()

instance Default a => Default (Box a) where
    def = Box $ const def

instance Show a => Show (MemBox a) where
    show (MemBox f) = show f

makeLenses ''MachinePO'

po_table :: SystemSemantics' expr -> SeqMap
po_table sys = fmap (,Nothing) . uncurryMap $ proof_obligation <$> (mapKeys as_label $ sys!.machines)

_machineSyntax :: Prism' MachineWithProofs RawMachine
_machineSyntax = prism'
            (\m -> MachineWithProofs (m!.syntax.content') (m!.proofs)) 
            (\(MachineWithProofs m ps) -> rightToMaybe $ withProofs ps $ check m)

_Syntax :: Prism' SystemSyntax SystemSemantics
_Syntax = below _machineSyntax.from content

compressingSystem :: Prism' CompressedSystem SystemSemantics
compressingSystem = packaged._Wrapped._Syntax

makeMachinePO' :: MachineAST' expr -> MachinePO' expr
makeMachinePO' x = MachinePO x def def def

raw_proof_obligation :: Controls machine (MachinePO' expr)
                     => machine -> Map Label Sequent
raw_proof_obligation = view $ content'.raw_proof_obligation_field.to unbox

proof_obligation :: Controls machine (MachinePO' expr)
                 => machine -> Map Label Sequent
proof_obligation = view (content'.proof_obligation_field.to unbox)

instance Controls (MachinePO' expr) (MachinePO' expr) where

--instance IsExpr expr => IsChecked (MachineAST' expr) (MachineAST' expr) where
--    check arse m = fromRight'' arse $ withPO _ _
--    content arse = _
    --func = 
instance (HasExpr expr,ZoomEq expr) => HasMachineBase (MachinePO' expr) expr where
    machineBase = syntax.content
instance (HasExpr expr,ZoomEq expr) => HasAbs_vars (MachinePO' expr) (Map Name Var) where
    abs_vars = machineBase.abs_vars
instance HasName (MachinePO' expr) Name where
    name = syntax.content'.name
instance (HasExpr expr,ZoomEq expr) => HasMachine (Machine' expr) expr where
    type Internal (Machine' expr) expr = MachinePO' expr
    empty_machine = fromSyntax . empty_machine
instance (HasExpr expr,ZoomEq expr) => HasMachine (MachinePO' expr) expr where
    type Internal (MachinePO' expr) expr = MachinePO' expr
    empty_machine = view content' . fromSyntax . empty_machine
instance (HasExpr expr,ZoomEq expr) => HasDefs (MachinePO' expr) (Map Name expr) where
    defs = machineBase.defs

instance HasExpr expr => HasInvariant (MachinePO' expr) where
    invariant m = do
        "inv1" ## keysSet (m^.proofs) `S.isSubsetOf` keysSet (raw_proof_obligation m)
    updateCache m = m 
            { _raw_proof_obligation_field = b
            , _proof_obligation_field = box $ 
                \() -> fromRight' $ proof_obligation' pos 
                        (fmap getExpr <$> m^.proofs) 
                        (getExpr <$> m^.syntax) }
        where
            b = box $ \() -> raw_machine_pos' $ m^.syntax
            pos = unbox b
#if MIN_VERSION_transformers(0,5,0)
instance F.Eq1 MachinePO' where
    liftEq = genericLiftEq
instance F.Show1 MachinePO' where
    liftShowsPrec = genericLiftShowsPrec
#else
instance Eq1 MachinePO' where
    eq1 = (==)
#endif
instance PrettyPrintable expr => PrettyPrintable (MachinePO' expr) where
instance NFData expr => NFData (MachinePO' expr) where
instance NFData expr => NFData (MachineWithProofs' expr) where
instance Serialize expr => Serialize (MachineWithProofs' expr) where
instance Show1 MachinePO' where
    showsPrec1 = showsPrec
instance NFData (Box a) where
    rnf x = seq x ()

deriving instance ZoomEq a => ZoomEq (MemBox a)

instance ZoomEq a => ZoomEq (Box a) where
    Box f .== Box g = f () .== g ()

instance ZoomEq expr => ZoomEq (MachinePO' expr) where

fromSyntax :: HasExpr expr => MachineAST' expr -> Machine' expr
fromSyntax m = check $ makeMachinePO' m

withProofs :: IsExpr expr
           => Map Label (ProofBase expr)
           -> MachineAST' expr
           -> Either [Error] (Machine' expr)
withProofs p m = fmap check' $ do
            let poBox = box $ \() -> raw_machine_pos' m
                pos = unbox poBox
            pos <- proof_obligation' pos p m
            return $ MachinePO m p poBox (box $ \() -> pos)

withProofs' :: (IsExpr expr,Pre)
            => Map Label Proof 
            -> MachineAST' expr
            -> Machine' expr
withProofs' p m = check $ makeMachinePO' m & proofs .~ p

withPOs :: HasExpr expr 
        => Map Label (Tactic Proof,LineInfo)
        -> MachineAST' expr 
        -> Either [Error] (Machine' expr)
withPOs ps m = fmap check' $ do
            let poBox = box $ \() -> raw_machine_pos' m
                pos = unbox poBox
                p = intersectionWith (\s (t,li) -> eitherToValidation $ runTactic li s t) pos ps
                f lbl (_,li) = Error ([Printf.s|proof obligation does not exist: %s\n\n%s|] 
                                        (pretty lbl) (unlines $ map pretty $ M.keys pos)) li
                errs = concat (p^.partsOf (traverse._Failure)) ++ elems (mapWithKey f $ ps `difference` pos)
                errs' | null errs = sequenceA p
                      | otherwise = Failure errs
            p <- validationToEither errs' 
            pos <- proof_obligation' pos (fmap getExpr <$> p) (getExpr <$> m)
            return $ MachinePO m p poBox (box $ \() -> pos)
            --proof_obligation_field (const $ box . const <$> proof_obligation' pos m) m'

verify_changes :: Machine -> Map Label (Bool,Sequent) -> IO (Map Label (Bool,Sequent), String,Int)
verify_changes m old_pos = do
        let pos = proof_obligation m
            new_pos = differenceWith f pos old_pos
        res <- verify_all new_pos
        let { h k p0 = (
            case M.lookup k res of
                Just b  -> (b,p0)
                Nothing -> old_pos ! k) }
        let all_pos = M.mapWithKey h pos 
        (res,_,_) <- format_result (M.map fst all_pos)
        return (all_pos,res, M.size new_pos)
    where
        f p0 (_,p1)
            | p0 == p1  = Nothing 
            | otherwise = Just p0

str_verify_machine :: HasExpr expr => Machine' expr -> IO (String,Int,Int)
str_verify_machine = str_verify_machine_with (const Just)

str_verify_machine_with :: HasExpr expr 
                        => (Label -> Sequent -> Maybe Sequent)
                        -> Machine' expr 
                        -> IO (String,Int,Int)
str_verify_machine_with opt m = do
        let pos = mapMaybeWithKey opt $ proof_obligation m
        xs <- verify_all pos
        format_result xs

smoke_test_machine :: Machine -> IO (String)
smoke_test_machine m = do
        let pos = proof_obligation m
        rs <- flip filterM (M.toList pos) $ \(lbl,po) -> do
            r <- smoke_test lbl po
            return $ r == Valid
        return $ L.unlines $ L.map (show . fst) rs

verify_machine :: Machine -> IO (Int, Int)
verify_machine m = do
    (s,i,j) <- str_verify_machine m
    putStrLn s
    return (i,j)

format_result :: Map Label Bool -> IO (String,Int,Int)
format_result xs' = do
        let rs    = L.map f $ M.toAscList xs'
            total = L.length rs
            passed = L.length $ L.filter fst rs
            xs = "passed " ++ (show passed) ++ " / " ++ show total
            ys = L.map snd rs ++ [xs]
        return (L.unlines ys, passed, total)
    where
        f (y,True)  = (True, "  o  " ++ pretty y)
        f (y,False) = (False," xxx " ++ pretty y)
