module Logic.Proof.Monad where

    -- Modules
import Logic.Expr
import Logic.Expr.Parser
import Logic.Expr.Printable
import Logic.Proof.Sequent
import Logic.Theories
import Logic.Theory

    -- Libraries
import Control.Lens hiding (Context)
import Control.Monad.RWS hiding ((<>))
import Control.Precondition

import Data.Map.Class as M
import Data.Set as S

import Utilities.Syntactic
import Utilities.Table

newtype SequentM a = SequentM (RWST () ([Sort],[Var],[Expr],[Context]) (ParserSetting,[Theory],Table Name Var) (Either [Error]) a)
    deriving (Functor,Applicative,Monad)

runSequent :: SequentM Expr -> Either [Error] Sequent
runSequent (SequentM cmd) =
    mkSequent <$> evalRWST cmd () (st, M.elems preludeTheories, M.empty)
    where
        st = theory_setting $ (empty_theory' "empty") { _extends =  preludeTheories }

runSequent' :: Pre
            => SequentM Expr -> Sequent
runSequent' = fromRight' . runSequent

mkSequent :: (Expr, ([Sort], [Var], [Expr], [Context])) -> Sequent
mkSequent (g, (s, vs, asm, ctx)) = empty_sequent 
        & goal .~ g 
        & nameless .~ asm
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)

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

assumeE :: Pre
        => StringLi -> SequentM ()
assumeE str = do
        setting <- SequentM $ use _1
        assume $ Right $ getExpr
            $ either (error . ("\n"++) . show_err) id
            $ parse_expr setting str

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

goalE :: Pre
        => StringLi -> SequentM Expr
goalE str = do
        setting <- SequentM $ use _1
        check $ Right $ getExpr
            $ either (error . ("\n"++) . show_err) id
            $ parse_expr setting str

declare :: Pre
        => String -> Type -> SequentM ExprP
declare n t = do
        declare' $ Var (fromString'' n) t

declare' :: Pre
        => Var -> SequentM ExprP
declare' v = do
        collectDeclaration $ Word v
        SequentM $ do
            tell ([],[v],[],[])
            _3 %= insert_symbol v
            _1.decls %= insert_symbol v
        return $ Right $ Word v

declareE :: Pre
        => StringLi -> SequentM ()
declareE str = do
    setting <- SequentM $ use _1
    let ctx = contextOf setting
    mapM_ declare' $ fmap snd $ run $ get_variables'' ctx str (line_info str)
    where
        run = either (error.("\n"++).show_err) id
