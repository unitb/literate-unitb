module Logic.Proof.Monad where

    -- Modules
import Logic.Expr
import Logic.Expr.Parser
import Logic.Expr.Printable
import Logic.Proof.Sequent
import Logic.Theories.Arithmetic
import Logic.Theory

    -- Libraries
import Control.Lens hiding (Context)
import Control.Monad.RWS hiding ((<>))
import Control.Precondition

import Data.Map.Class as M
import Data.Set as S

import Utilities.Table

newtype SequentM a = SequentM (RWS () ([Sort],[Var],[Expr],[Context]) (ParserSetting,[Theory],Table Name Var) a)
    deriving (Functor,Applicative,Monad)

runSequent :: SequentM Expr -> Sequent
runSequent (SequentM cmd) = empty_sequent 
        & goal .~ g 
        & nameless .~ asm
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    where
        (g,(s,vs,asm,ctx)) = evalRWS cmd () (st,[arithmetic,basic_theory],M.empty)
        st = theory_setting $ (empty_theory' "empty") { _extends = 
                symbol_table [arithmetic,basic_theory] }

updateSetting :: SequentM ()
updateSetting = SequentM $ do
    ts <- use _2
    _1 .= theory_setting (empty_theory' "empty") { _extends = 
                symbol_table ts }
    ds <- use _3
    _1.decls %= M.union ds

include :: Theory -> SequentM ()
include t = do
    SequentM $ do
        tell ([],[],M.elems $ theory_facts t,[theory_ctx t])
        _2 %= (t:)
    updateSetting

assume :: Pre
       => ExprP -> SequentM ()
assume e = do
        let e' = fromRight' e
        collectDeclaration e'
        SequentM $ tell ([],[],[e'],[])

assumeQ :: Pre
        => (ParserSetting -> DispExpr) -> SequentM ()
assumeQ qexpr = do
        setting <- SequentM $ use _1
        assume $ Right $ getExpr $ qexpr setting

collectDeclaration :: Expr -> SequentM ()
collectDeclaration e = SequentM $ do
        let ts = types_of e^.partsOf (to S.toList.traverse.foldSorts)
        tell (ts,[],[],[])

check :: Pre
      => ExprP -> SequentM Expr
check e = do
        let e' = fromRight' e
        collectDeclaration e'
        return e'

checkQ :: Pre
        => (ParserSetting -> DispExpr) -> SequentM Expr
checkQ qexpr = do
        setting <- SequentM $ use _1
        check $ Right $ getExpr $ qexpr setting

declare :: Pre
        => String -> Type -> SequentM ExprP
declare n t = do
        let v = Var (fromString'' n) t
        collectDeclaration $ Word v
        SequentM $ do
            tell ([],[v],[],[])
            _3 %= insert_symbol (z3Var n t)
            _1.decls %= insert_symbol (z3Var n t)
        return $ Right $ Word v
