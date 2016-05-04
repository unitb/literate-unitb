module Logic.Expr.Parser.Internal.Setting where

import Logic.Expr
import Logic.Operator
import Logic.Theory

import Control.DeepSeq

import GHC.Generics ( Generic )

import Utilities.Table

import Control.Lens hiding ( Context )
import           Data.Map.Class hiding ( map )
import qualified Data.Map.Class as M
import           Control.Monad.State as ST ( State, execState )

data ParserSetting = PSetting 
    { _language :: Notation
    , _is_step  :: Bool
    , _parserSettingSorts    :: Table Name Sort
    , _decls    :: Table Name Var
    , _dum_ctx  :: Table Name Var
    , _primed_vars   :: Table Name Var
    , _free_dummies  :: Bool
    , _expected_type :: Maybe Type
    }
    deriving (Generic,Eq,Show)

makeLenses ''ParserSetting
makeFields ''ParserSetting

instance PrettyPrintable ParserSetting where
    pretty _ = "<parser-setting>"

instance NFData ParserSetting

default_setting :: Notation -> ParserSetting
default_setting n = PSetting 
    { _language = n
    , _decls = M.empty
    , _parserSettingSorts = M.empty
    , _primed_vars = M.empty
    , _dum_ctx = M.empty
    , _is_step = False
    , _free_dummies = False
    , _expected_type = (Just bool)
    }

makeSetting :: Notation -> State ParserSetting a -> ParserSetting
makeSetting n cmd = execState cmd (default_setting n)

setting_from_context :: Notation -> Context -> ParserSetting
setting_from_context notation ctx' = makeSetting notation $ do
        sorts .= ctx^.sorts
        decls .= ctx^.constants
        dum_ctx .= ctx^.dummies
    where
        ctx = defsAsVars ctx'

with_vars :: ParserSetting -> Table Name Var -> ParserSetting
with_vars setting vs = setting & decls %~ (vs `union`)

mkSetting :: Notation 
          -> Table Name Sort    -- Types
          -> Table Name Var     -- Plain variables
          -> Table Name Var     -- Primed variables
          -> Table Name Var     -- Dummy variables
          -> ParserSetting
mkSetting notat sorts plVar prVar dumVar = (default_setting notat)
        { _parserSettingSorts = sorts
        , _decls = (plVar `union` prVar)
        , _primed_vars = primeAll prVar
        , _dum_ctx = dumVar }

theory_setting :: Theory -> ParserSetting
theory_setting th = (setting_from_context (th_notation th) (theory_ctx th))
