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

import Data.List as L
import Data.Map.Class as M
import Data.Set as S

import GHC.Generics.Instances

import Utilities.Syntactic
import Utilities.Table

type SequentM = SequentM' Expr
newtype SequentM' expr a = SequentM (
        RWST
          ()
          (SeqDefinitions expr)
          (ParserSetting,[Theory],Table Name Var)
          (Either [Error]) a)
    deriving (Functor,Applicative,Monad)

type DispSequent = HOSequent DispExpr

type SequentWithWD = SequentWithWD' Expr
type DispSequentWithWD = SequentWithWD' DispExpr
data SequentWithWD' expr = SequentWithWD
    { _wd :: Sequent
    , _goal :: HOSequent expr }

data SeqDefinitions expr = SeqDefinitions
    { _seqDefinitionsSorts :: [Sort]
    , _vars  :: [Var]
    , _asms  :: Table Label expr
    , _facts :: [expr]
    , _ctxs  :: [Context] }
    deriving Generic

instance Monoid (SeqDefinitions expr) where
    mempty = genericMEmpty
    mappend = genericMAppend
    mconcat = genericMConcat

makeLenses ''SeqDefinitions
makeFields ''SeqDefinitions

runSequent_ :: HasExpr expr => SequentM' expr expr -> Either [Error] (HOSequent expr)
runSequent_ = fmap _goal . runSequent

runSequent :: HasExpr expr
           => SequentM' expr expr
           -> Either [Error] (SequentWithWD' expr)
runSequent (SequentM cmd) =
    mkSequent <$> evalRWST cmd () (parser, M.elems preludeTheories, M.empty)
    where
        parser = theory_setting $ (empty_theory' "empty") { _extends =  preludeTheories }

runSequent' :: Pre
            => SequentM Expr -> SequentWithWD
runSequent' = fromRight' . runSequent

mkSequent :: HasExpr expr => (expr, SeqDefinitions expr) -> SequentWithWD' expr
mkSequent (g, (SeqDefinitions s vs asm thms ctx)) = SequentWithWD
    { _goal = empty_sequent
        & goal .~ g
        & named .~ asm
        & nameless .~ thms
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    , _wd = empty_sequent
        & goal .~ well_definedness (zall (getExpr <$> M.elems asm) `zimplies` getExpr g)
        & nameless .~ L.map getExpr thms
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    }

updateSetting :: SequentM' expr ()
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

include :: FromDispExpr expr
        => Theory -> SequentM' expr ()
include t = do
    SequentM $ do
        --tell ([],[],M.elems $ theory_facts t,[theory_ctx t])
        tell' $ do
            facts .= L.map (fromDispExpr . DispExpr "") (M.elems $ theory_facts t)
            ctxs .= [theory_ctx t]
        _2 %= (t:)
    updateSetting

assume :: Pre
       => String -> ExprP -> SequentM ()
assume s e = assume' s (fromRight' e)

assume' :: HasExpr expr
        => String -> expr -> SequentM' expr ()
assume' lbl e = do
        collectDeclaration e
        SequentM $ tell' $ asms .= M.singleton (label lbl) e -- tell ([],[],[e'],[])

assumeQ :: (FromDispExpr expr,HasExpr expr, Pre)
        => String -> (ParserSetting -> DispExpr) -> SequentM' expr ()
assumeQ lbl qexpr = do
        setting <- SequentM $ use _1
        assume' lbl $ fromDispExpr $ qexpr setting

assumeE :: (FromDispExpr expr,HasExpr expr)
        => (String, StringLi) -> SequentM' expr ()
assumeE (lbl, str) = do
        setting <- SequentM $ use _1
        de <- hoistEither $ parse_expr setting str
        let e = fromDispExpr de
        collectDeclaration e
        SequentM $ tell' $ asms .= M.singleton (label lbl) e -- tell ([],[],[e],[])

collectDeclaration :: HasExpr expr
                   => expr
                   -> SequentM' expr0 ()
collectDeclaration e = SequentM $ do
        let ts = types_of (getExpr e)^.partsOf (to S.toList.traverse.foldSorts)
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
        de <- checkE' str
        let e = getExpr de
        collectDeclaration e
        return e

checkE' :: StringLi -> SequentM' expr DispExpr
checkE' str = do
        setting <- SequentM $ use _1
        hoistEither $ parse_expr setting str

declare :: Pre
        => String -> Type -> SequentM ExprP
declare n t = do
        declare' $ Var (fromString'' n) t

declare' :: Pre
         => Var -> SequentM' expr ExprP
declare' v = do
        collectDeclaration $ Word v
        SequentM $ do
            tell' $ vars .= [v] -- tell ([],[v],[],[])
            _3 %= insert_symbol v
            _1.decls %= insert_symbol v
        return $ Right $ Word v

declareE :: StringLi -> SequentM' expr ()
declareE str = do
    setting <- SequentM $ use _1
    let ctx = contextOf setting
    vs <- hoistEither $ get_variables'' ctx str (line_info str)
    mapM_ declare' . fmap snd $ vs

hoistEither :: Either [Error] a -> SequentM' expr a
hoistEither = SequentM . lift
