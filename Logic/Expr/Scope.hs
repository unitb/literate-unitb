{-# LANGUAGE TypeFamilies #-}
module Logic.Expr.Scope where

    -- Modules
import Logic.Expr.Label
import Logic.Expr.Variable

    -- Libraries
import Control.Lens
import Control.Monad.Reader.Class

import Data.Default
import Data.List
import Data.Map as M

import Text.Printf

import Utilities.Instances

data VisibleVars = VisibleVars
        { _visibleVarsConstants :: Map String Var
        , _visibleVarsAbs_vars  :: Map String Var
        , _vars      :: Map String Var
        , _prefix    :: [String]
        } deriving (Generic,Show)

type ScopeCorrectness  = ScopeCorrectnessM [(String,String)]
type ScopeCorrectnessM = ((->) VisibleVars)

class HasScope a where
    scopeCorrect' :: a -> ScopeCorrectness

makeLenses ''VisibleVars
makeFields ''VisibleVars

instance Default VisibleVars where
    def = genericDefault

scopeCorrect'' :: (HasScope a, Show lbl) => lbl -> a -> ScopeCorrectness
scopeCorrect'' lbl x = withPrefix (show lbl) $ scopeCorrect' x

withPrefix :: String 
           -> ScopeCorrectnessM a 
           -> ScopeCorrectnessM a
withPrefix lbl = local (prefix %~ (lbl:))

withVars :: (Foldable f) 
         => f Var 
         -> ScopeCorrectnessM a
         -> ScopeCorrectnessM a
withVars = withVars' constants

withVars' :: (Foldable f) 
          => Lens' VisibleVars (Map String Var) -> f Var 
          -> ScopeCorrectnessM a
          -> ScopeCorrectnessM a
withVars' ln vs = local (ln %~ M.union (symbol_table vs))

withAbstract :: ScopeCorrectnessM a -> ScopeCorrectnessM a
withAbstract = local (\x -> x & vars %~ M.union (x^.abs_vars))

withPrimes :: ScopeCorrectnessM a -> ScopeCorrectnessM a
withPrimes cmd = do
    x <- ask
    withVars' vars (primeAll $ x^.vars) $ withVars' abs_vars (primeAll $ x^.abs_vars) cmd

areVisible :: (Show e,Foldable f) 
           => [Getting (Map String Var) VisibleVars (Map String Var)]
           -> f Var -> e -> ScopeCorrectness
areVisible ln vars' e = do
    vs <- foldMap view ln 
    let pre  = printf "\n free vars = %s\n declared  = %s\n diff      = %s"
                (show $ M.toList vars)
                (show $ M.toList vs)
                (show $ M.toList $ vars `M.difference` vs)
        vars = symbol_table vars'
    if vars `isSubmapOf` vs
        then return []
        else withPrefix pre $ do 
            pre <- views prefix $ intercalate " - " . reverse
            return [(pre,show e)]

scopeCorrect :: HasScope a => a -> [(String,String)]
scopeCorrect x = scopeCorrect' x def
