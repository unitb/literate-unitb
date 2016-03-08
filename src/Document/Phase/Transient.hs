{-# LANGUAGE TypeOperators #-}
module Document.Phase.Transient where

    --
    -- Modules
    --
import Document.Phase as P
import Document.Phase.Types
import Document.Proof
import Document.Visitor

import Latex.Parser hiding (contents)

import Logic.Expr

import UnitB.Syntax as AST

    --
    -- Libraries
    --
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS as RWS ( RWS )

import Control.Lens as L hiding ((|>),(<.>),(<|),indices,Context)

import Data.Either.Validation
import qualified Data.Maybe as MM
import           Data.List as L hiding ( union, insert, inits )
import qualified Data.List.NonEmpty as NE
import Data.Map.Class   as M hiding ( (\\) )

import Text.Printf.TH

import Utilities.Syntactic
import Utilities.Table

tr_hintV :: HasMachineP2 mch
         => mch
         -> Table Name Var
         -> NonEmpty EventId
         -> LatexDoc
         -> Either [Error] TrHint
tr_hintV p2 vs evts doc = validationToEither $ eitherToValidation r <* nonNullError es
    where
        (r,es) = runM (tr_hint p2 vs (as_label <$> evts) doc) (line_info doc)

nonNullError :: [e] -> Validation [e] ()
nonNullError [] = pure ()
nonNullError es = Failure es

tr_hint :: HasMachineP2 mch
        => mch
        -> Table Name Var
        -> NonEmpty Label
        -> LatexDoc
        -> M TrHint
tr_hint p2 vs lbls thint = do
    tr@(TrHint wit _)  <- toEither $ tr_hint' p2 vs lbls thint empty_hint
    evs <- get_events p2 $ NE.toList lbls
    let vs = L.map (view pIndices p2 !) evs
        err e ind = ( not $ M.null diff
                    , [printf|A witness is needed for %s in event '%s'|] 
                        (intercalate "," $ render <$> keys diff) (show e))
            where
                diff = ind `M.difference` wit
    toEither $ error_list 
        $ zipWith err evs vs
    return tr

tr_hint' :: HasMachineP2 mch
         => mch
         -> Table Name Var
         -> NonEmpty Label
         -> LatexDoc
         -> TrHint
         -> RWS LineInfo [Error] () TrHint
tr_hint' p2 fv lbls = visit_doc []
        [ ( "\\index"
          , CmdBlock $ \(x, texExpr) (TrHint ys z) -> do
                evs <- _unM $ get_events p2 lbls
                let inds = p2^.pIndices
                vs <- _unM $ bind_all evs 
                    ([printf|'%s' is not an index of '%s'|] (render x) . show) 
                    (\e -> x `M.lookup` (inds ! e))
                let Var _ t = NE.head vs
                    ind = prime $ Var x t
                    x'  = addPrime x
                expr <- _unM $ hoistEither $ parse_expr' 
                    ((p2^.pMchSynt) `with_vars` insert x' ind fv) 
                    texExpr
                return $ TrHint (insert x (t, expr) ys) z)
        , ( "\\lt"
          , CmdBlock $ \(Identity prog) (TrHint ys z) -> do
                let msg = [printf|Only one progress property needed for '%s'|]
                _unM $ toEither $ error_list 
                    [ ( not $ MM.isNothing z
                      , msg $ show $ NE.toList lbls )
                    ]
                return $ TrHint ys (Just prog))
        ]

get_event :: (HasMachineP1 phase,MonadReader LineInfo m,MonadError [Error] m) 
          => phase -> Label -> m EventId
get_event p2 ev_lbl = do
        let evts = p2^.pEventIds
        bind
            ([printf|event '%s' is undeclared|] $ show ev_lbl)
            $ ev_lbl `M.lookup` evts

get_abstract_event :: HasMachineP1 phase => phase -> EventId -> M EventId
get_abstract_event p2 ev_lbl = do
        let evts = p2^.pEventSplit & M.mapKeys as_label . M.mapWithKey const
        bind
            ([printf|event '%s' is undeclared|] $ show ev_lbl)
            $ as_label ev_lbl `M.lookup` evts

get_events :: (Traversable f,MonadReader r m,Syntactic r,MonadError [Error] m,HasMachineP2 mch)
           => mch -> f Label -> m (f EventId)
get_events p2 ev_lbl = do
            let evts = p2^.pEventIds
            bind_all ev_lbl
                ([printf|event '%s' is undeclared|] . show)
                $ (`M.lookup` evts)
