module Logic.Proof.Monad where

    -- Modules
import Logic.Expr
import Logic.Proof.Sequent
import Logic.Theory

    -- Libraries
import Control.Lens hiding (Context)
import Control.Monad.Writer
import Control.Precondition

import Data.Map.Class as M
import Data.Set as S

newtype SequentM a = SequentM (Writer ([Sort],[Var],[Expr],[Context]) a)
    deriving (Functor,Applicative,Monad)

runSequent :: SequentM Expr -> Sequent
runSequent (SequentM cmd) = empty_sequent 
        & goal .~ g 
        & nameless .~ asm
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    where
        (g,(s,vs,asm,ctx)) = runWriter cmd

include :: Theory -> SequentM ()
include t = SequentM $ tell ([],[],M.elems $ theory_facts t,[theory_ctx t])

assume :: Pre
       => ExprP -> SequentM ()
assume e = do
        let e' = fromRight' e
        collectDeclaration e'
        SequentM $ tell ([],[],[e'],[])

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

declare :: Pre
        => String -> Type -> SequentM ExprP
declare n t = do
        let v = Var (fromString'' n) t
        collectDeclaration $ Word v
        SequentM $ tell ([],[v],[],[])
        return $ Right $ Word v
