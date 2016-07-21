module Logic.Proof.Monad where

    -- Modules
import Logic.Expr
import Logic.Expr.Parser
import Logic.Expr.Printable
import Logic.Proof.Sequent
import Logic.Theories
import Logic.Theory
import Logic.WellDefinedness

    -- Libraries
import Control.Lens hiding (Context)
import Control.Monad.RWS hiding ((<>))
import Control.Monad.State
import Control.Precondition

import Data.Map.Class as M
import Data.Set as S

import GHC.Generics.Instances

import Utilities.Syntactic
import Utilities.Table

newtype SequentM a = SequentM (RWST () SeqDefinitions (ParserSetting,[Theory],Table Name Var) (Either [Error]) a)
    deriving (Functor,Applicative,Monad)

type SequentWithWD = SequentWithWD' Sequent
data SequentWithWD' a = SequentWithWD
    { _wd :: a 
    , _goal :: a }
    deriving (Eq, Show, Generic)

data SeqDefinitions = SeqDefinitions
    { _seqDefinitionsSorts :: [Sort] 
    , _vars  :: [Var] 
    , _asms  :: [Expr] 
    , _facts :: [Expr] 
    , _ctxs  :: [Context] }
    deriving Generic

instance Monoid SeqDefinitions where
    mempty = genericMEmpty
    mappend = genericMAppend
    mconcat = genericMConcat

makeLenses ''SeqDefinitions
makeFields ''SeqDefinitions

runSequent_ :: SequentM Expr -> Either [Error] Sequent
runSequent_ = fmap _goal . runSequent

runSequent :: SequentM Expr -> Either [Error] SequentWithWD
runSequent (SequentM cmd) =
    mkSequent <$> evalRWST cmd () (parser, M.elems preludeTheories, M.empty)
    where
        parser = theory_setting $ (empty_theory' "empty") { _extends =  preludeTheories }

runSequent' :: Pre
            => SequentM Expr -> SequentWithWD
runSequent' = fromRight' . runSequent

mkSequent :: (Expr, SeqDefinitions) -> SequentWithWD
mkSequent (g, (SeqDefinitions s vs asm thms ctx)) = SequentWithWD
    { _goal = empty_sequent 
        & goal .~ g 
        & nameless .~ thms ++ asm
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    , _wd = empty_sequent
        & goal .~ well_definedness (zall asm `zimplies` g)
        & nameless .~ thms
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    }

updateSetting :: SequentM ()
updateSetting = SequentM $ do
    ts <- use _2
    _1 .= theory_setting (empty_theory' "empty") { _extends = 
                symbol_table ts }
    ds <- use _3
    _1.decls %= M.union ds

tell' :: (Monoid w,MonadWriter w m)
      => State w k
      -> m ()
tell' cmd = tell $ execState cmd mempty

include :: Theory -> SequentM ()
include t = do
    SequentM $ do
        --tell ([],[],M.elems $ theory_facts t,[theory_ctx t])
        tell' $ do
            facts .= M.elems (theory_facts t)
            ctxs .= [theory_ctx t]
        _2 %= (t:)
    updateSetting

assume :: Pre
       => ExprP -> SequentM ()
assume e = do
        let e' = fromRight' e
        collectDeclaration e'
        SequentM $ tell' $ asms .= [e'] -- tell ([],[],[e'],[])

assumeQ :: Pre
        => (ParserSetting -> DispExpr) -> SequentM ()
assumeQ qexpr = do
        setting <- SequentM $ use _1
        assume $ Right $ getExpr $ qexpr setting

assumeE :: StringLi -> SequentM ()
assumeE str = do
        setting <- SequentM $ use _1
        case parse_expr setting str of
            Left  es -> SequentM . lift . Left $ es
            Right de -> do
                let e = getExpr de
                collectDeclaration e
                SequentM $ tell' $ asms .= [e] -- tell ([],[],[e],[])

collectDeclaration :: Expr -> SequentM ()
collectDeclaration e = SequentM $ do
        let ts = types_of e^.partsOf (to S.toList.traverse.foldSorts)
        tell' $ sorts .= ts -- tell (ts,[],[],[])

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

checkE :: StringLi -> SequentM Expr
checkE str = do
        setting <- SequentM $ use _1
        case parse_expr setting str of
            Left  es -> SequentM . lift . Left $ es
            Right de -> do
                let e = getExpr de
                collectDeclaration e
                return e

declare :: Pre
        => String -> Type -> SequentM ExprP
declare n t = do
        declare' $ Var (fromString'' n) t

declare' :: Pre
        => Var -> SequentM ExprP
declare' v = do
        collectDeclaration $ Word v
        SequentM $ do
            tell' $ vars .= [v] -- tell ([],[v],[],[])
            _3 %= insert_symbol v
            _1.decls %= insert_symbol v
        return $ Right $ Word v

declareE :: StringLi -> SequentM ()
declareE str = do
    setting <- SequentM $ use _1
    let ctx = contextOf setting
    case get_variables'' ctx str (line_info str) of
        Left  es -> SequentM . lift . Left $ es
        Right vs -> do 
            mapM_ declare' . fmap snd $ vs
