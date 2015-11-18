{-# LANGUAGE ViewPatterns 
    , OverloadedStrings
    #-}
module Documentation.SummaryGen 
    ( produce_summaries
    , event_summary' 
    , getListing
    , safety_sum
    , liveness_sum )
where

    -- Modules
import UnitB.AST
import UnitB.Expr hiding ((</>))

    -- Libraries
import Control.Lens hiding ((<.>),indices)

import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Reader (ReaderT(..),runReaderT)

import Data.Default
import Data.List as L ( intercalate,null
                      , map,unlines,lines )
import Data.List.NonEmpty as NE
import Data.Map as M hiding (map)
import qualified Data.Map as M

import System.FilePath

import Prelude hiding (writeFile,readFile)

import Utilities.FileSystem
import Utilities.Format

newtype Doc a = Doc { getDoc :: forall io. FileSystem io => ReaderT FilePath io a }
    deriving (Functor)
    -- Reader parameters:
    --      AST -> LaTeX conversions
    --      path for listing creation
type M = RWS Bool [String] ()
    --      AST -> LaTeX conversions
    --      should we strike out expressions?

data ExprDispOpt label expr = ExprDispOpt
        { _makeDoc :: label -> M ()                 -- Command to produce documentating comments
        , _makeRef :: EventId -> label -> M String  -- How to convert a label to a LaTeX reference?
        , _makeString :: expr -> M String }         -- How to convert (AST) type `a` to LaTeX?

makeLenses ''ExprDispOpt

instance Applicative Doc where
    pure x = Doc $ pure x
    Doc f <*> Doc x = Doc $ f <*> x

instance Monad Doc where
    Doc m >>= f = Doc $ m >>= getDoc . f
instance MonadReader FilePath Doc where
    ask = Doc ask
    local f (Doc m) = Doc $ local f m
instance FileSystem Doc where
    liftFS f = NoParam $ Doc $ lift $ getNoParam f
    lift2FS f = OneParam $ \g -> Doc $ ReaderT $ \fn -> getOneParam f $ \x -> runReaderT (getDoc $ g x) fn

defOptions :: Show label => (expr -> M String) -> ExprDispOpt label expr
defOptions f = ExprDispOpt
            { _makeDoc = const $ return () 
            , _makeString = f 
            , _makeRef = \pre lbl -> return $ format "\\eqref{{0}}" (show pre ++ show lbl) }

instance Show label => Default (ExprDispOpt label Expr) where
    def = defOptions get_string'

show_removals :: Bool
show_removals = True

runDoc :: FileSystem io => Doc a -> FilePath -> io a
runDoc (Doc cmd) = runReaderT cmd

produce_summaries :: FileSystem io 
                  => FilePath -> System -> io ()
produce_summaries path sys = do
        createDirectoryIfMissing True path'
        runDoc (do
            forM_ (M.elems ms) $ \m -> do
                machine_summary sys m
                properties_summary m
                forM_ (M.toList $ nonSkipUpwards m) $ \(lbl,evt) -> do
                    event_summary m lbl evt
            ) path
    where
        ms = sys!.machines
        path' = dropExtension path

make_file :: FilePath -> M () -> Doc ()
make_file fn cmd = do
    path <- ask
    let xs = snd $ execRWS cmd False ()
        root = format "%!TEX root=../{0}" (takeFileName path)
    writeFile (dropExtension path </> fn) 
        $ L.unlines $ root : xs

keyword :: String -> String
keyword kw = format "\\textbf{{0}}" kw

machine_summary :: System -> Machine -> Doc ()
machine_summary sys m = do
    path <- ask
    make_file fn $ 
        block $ do
            item $ tell [keyword "machine" ++ " " ++ show (_name m)]
            item $ refines_clause sys m
            item $ variable_sum m
            unless (M.null $ _inv $ m!.props) 
                $ item $ input path $ inv_file m
            unless (M.null $ _inv_thm $ m!.props) 
                $ item $ input path $ inv_thm_file m
            unless (M.null $ _progress $ m!.props) 
                $ item $ input path $ live_file m
            unless (M.null $ _safety $ m!.props) 
                $ item $ input path $ saf_file m
            unless (M.null $ _transient $ m!.props)
                $ item $ input path $ transient_file m
            unless (M.null $ _constraint $ m!.props)
                $ item $ input path $ constraint_file m
            item $ do
                tell [keyword "events"]
                let evts = keys $ nonSkipUpwards m
                unless (L.null evts) $
                    block $ forM_ evts $ \k -> do
                        item $ input path $ event_file_name m k
            item $ kw_end
    where
        fn = "machine_" ++ (m!.name) <.> "tex"

prop_file_name :: Machine -> String
prop_file_name m = "machine_" ++ (m!.name) ++ "_props" <.> "tex"

indent :: Int -> String -> String
indent n xs = intercalate "\n" $ L.map (margin ++) $ L.lines xs
    where
        margin = replicate n ' '

item :: M () -> M ()
item cmd = do
    let f [] = []
        f xs = ["  \\item " ++ intercalate "\n" (L.map (indent 2) xs)]
    censor f cmd

properties_summary :: Machine -> Doc ()
properties_summary m = do
        let prop = m!.props
        path <- ask
        make_file (inv_file m) $ invariant_sum m
        make_file (inv_thm_file m) $ invariant_thm_sum prop
        make_file (live_file m) $ liveness_sum m
        make_file (transient_file m) $ transient_sum m
        make_file (saf_file m) $ safety_sum prop
        make_file (constraint_file m) $ constraint_sum m
        make_file fn $ block $ do
            item $ input path $ inv_file m
            item $ input path $ inv_thm_file m
            item $ input path $ live_file m
            item $ input path $ saf_file m
            item $ input path $ transient_file m
            item $ input path $ constraint_file m
    where
        fn = prop_file_name m

inv_file :: Machine -> String
inv_file m  = "machine_" ++ (m!.name) ++ "_inv" <.> "tex"

inv_thm_file :: Machine -> String
inv_thm_file m  = "machine_" ++ (m!.name) ++ "_thm" <.> "tex"

live_file :: Machine -> String
live_file m = "machine_" ++ (m!.name) ++ "_prog" <.> "tex"

transient_file :: Machine -> String
transient_file m = "machine_" ++ (m!.name) ++ "_trans" <.> "tex"

saf_file :: Machine -> String
saf_file m  = "machine_" ++ (m!.name) ++ "_saf" <.> "tex"

constraint_file :: Machine -> String
constraint_file m  = "machine_" ++ (m!.name) ++ "_co" <.> "tex"

getListing :: M () -> String
getListing cmd = L.unlines $ snd $ execRWS cmd False ()

input :: FilePath -> String -> M ()
input path fn = do
    tell [format "\\input{{0}/{1}}" (takeBaseName path) $ dropExtension fn]

kw_end :: M ()
kw_end = tell ["\\textbf{end} \\\\"]

event_file_name :: Machine -> EventId -> FilePath
event_file_name m lbl = ((m!.name) ++ "_" ++ rename lbl) <.> "tex"
    where
        rename lbl = L.map f $ show lbl
        f ':' = '-'
        f x   = x

comment_of :: Machine -> DocItem -> M ()
comment_of m key = do
    item $ do
        case key `M.lookup` (m!.comments) of
            Just cmt -> block $ item $ tell [format "{0}" cmt]
            Nothing -> return ()

event_summary' :: Machine -> EventId -> EventMerging' -> M ()
event_summary' m lbl e = do
        index_sum lbl e
        comment_of m (DocEvent lbl)
        block $ do
            item $ csched_sum lbl e
            item $ fsched_sum lbl e
            item $ param_sum e
            item $ guard_sum lbl e
            item $ act_sum lbl e
            item $ kw_end

event_summary :: Machine -> EventId -> EventMerging' -> Doc ()
event_summary m lbl e = make_file fn $ 
        event_summary' m lbl e
    where
        fn = event_file_name m lbl

refines_clause :: System -> Machine -> M ()
refines_clause sys m = do
    case join $ _name m `M.lookup` (sys!.ref_struct) of
        Nothing -> return ()
        Just anc -> tell [keyword "refines" ++ " " ++ show anc]

block :: M () -> M ()
block cmd = do
    tell ["\\begin{block}"]
    cmd
    tell ["\\end{block}"]

variable_sum :: Machine -> M ()
variable_sum m = section (keyword "variables") $ 
    unless (M.null (m!.variables) && M.null (m!.abs_vars)) $
    block $ do
        when show_removals $ 
            forM_ (keys $ view' abs_vars m `M.difference` view' variables m) $ \v -> do
                item $ tell [format "${0}$\\quad(removed)" v]
                comment_of m (DocVar v)
        forM_ (keys $ view' variables m) $ \v -> do
            item $ tell [format "${0}$" v]
            comment_of m (DocVar v)

invariant_sum :: Machine -> M ()
invariant_sum m = do
        let prop = m!.props
        section kw_inv $ put_all_expr_with (makeDoc .= comment_of m . DocInv) "" (M.toList $ prop^.inv) 
    where
        kw_inv = "\\textbf{invariants}"
        
invariant_thm_sum :: PropertySet -> M ()
invariant_thm_sum prop = 
        section kw_thm $ put_all_expr "" (M.toList $ prop^.inv_thm)
    where
        kw_thm = "\\textbf{invariants} (theorems)"

liveness_sum :: Machine -> M ()
liveness_sum m = do
        let prop = m!.props
        section kw $ put_all_expr' toString "" (M.toList $ prop^.progress) 
    where
        kw = "\\textbf{progress}"
        toString (LeadsTo _ p q) = do
            p' <- get_string' p
            q' <- get_string' q
            return $ format "{0} \\quad \\mapsto\\quad {1}" p' q'

safety_sum :: PropertySet -> M ()
safety_sum prop = do
        section kw $ put_all_expr' toString "" (M.toList $ prop^.safety)
    where
        kw = "\\textbf{safety}"
        toString (Unless _ p q) = do
            p' <- get_string' p
            q' <- get_string' q
            return $ format "{0} \\textbf{\\quad unless \\quad} {1}" p' q'

transient_sum :: Machine -> M ()
transient_sum m = do
        let prop = m!.props
        section kw $ put_all_expr' toString "" (M.toList $ prop^.transient) 
    where
        kw = "\\textbf{transient}"
        toString (Tr _ p evts hint) = do -- do
            let TrHint sub lt = hint
                evts' :: String
                evts' = intercalate "," $ L.map (format "\\ref{{0}}") (NE.toList evts)
            sub' <- forM (M.toList sub) $ \(v,p) -> do
                p <- get_string' $ snd p
                return (v,p)
            let isNotIdent n (getExpr -> Word (Var n' _)) = n /= n'
                isNotIdent _ _ = True
                sub'' :: String
                sub'' 
                    | M.null $ M.filterWithKey isNotIdent $ M.map snd sub = ""
                    | otherwise  = format ": [{0}]" (intercalate ", " $ L.map (uncurry $ format "{0} := {0}'~|~{1}") $ sub' :: String)
                lt' :: String
                lt' = maybe "" (format ", with \\eqref{{0}}") lt
            p <- get_string' p
            return $ format "{0} \\qquad \\text{({1}${2}${3})}" 
                p evts' sub'' lt'
            -- p' <- get_string' p
            -- q' <- get_string' q
            -- return $ format "{0} \\quad \\mapsto\\quad {1}" p' q'

constraint_sum :: Machine -> M ()
constraint_sum m = do
        let prop = m!.props
        section kw $ put_all_expr' toString "" (M.toList $ prop^.constraint)
    where
        kw = "\\textbf{safety}"
        toString (Co _ p) = do
            get_string' p

format_formula :: String -> M String
format_formula str = do
        sout <- ask    -- Strike out the formula?
        let sout' 
                | sout      = "\\sout"
                | otherwise = ""
        return $ intercalate "\n" $ L.map (++ " %") $ L.lines $ sout' ++ "{$" ++ f str ++ "$}"
            -- what is the point of ending the L.lines with '%' ?
    where
        f xs = concatMap g xs
        g '&' = ""
        g x = [x]

get_string' :: Expr -> M String
get_string' e = do
    return $ prettyPrint e

put_expr :: ExprDispOpt label expr     
         -> EventId             -- label prefix (for LaTeX cross referencing)
         -> (label,expr)        -- AST and its label
         -> M ()
put_expr opts pre (lbl,e) = do
        ref <- (opts^.makeRef) pre lbl
        --let ref :: String
        --    ref = case lbl of
        --            Nothing -> format "(\\ref{{0}}/default)" pre
        --            Just lbl -> format "\\eqref{{0}}" (show pre ++ show lbl)
        expr  <- format_formula =<< (opts^.makeString $ e)
        tell [format "\\item[ {0} ]{1}" 
                    ref expr]
        opts^.makeDoc $ lbl

put_all_expr' :: Show label => (a -> M String) -> EventId -> [(label, a)] -> M ()
put_all_expr' f = put_all_expr_with' f (return ())

put_all_expr_with' :: Show label
                       => (expr -> M String)
                       -> State (ExprDispOpt label expr) ()
                       -> EventId 
                       -> [(label, expr)] -> M ()
put_all_expr_with' toString opts pre xs
    | L.null xs = return ()
    | otherwise = 
        block $ forM_ xs $ put_expr (execState opts $ defOptions toString) pre

put_all_expr :: EventId -> [(Label,Expr)] -> M ()
put_all_expr = put_all_expr' get_string'

put_all_expr_with :: State (ExprDispOpt Label Expr) () 
                      -> EventId -> [(Label, Expr)] -> M ()
put_all_expr_with opts = put_all_expr_with' get_string' opts

section :: String -> M () -> M ()
section kw cmd = do
    let f [] = []
        f xs = kw:xs
    censor f cmd

index_sum :: EventId -> EventMerging' -> M ()
index_sum lbl e = tell ["\\noindent \\ref{" ++ show lbl ++ "} " ++ ind ++ " \\textbf{event}"]
    where
        ind 
            | M.null $ e^.indices = ""
            | otherwise           = "[" ++ intercalate "," (L.map (view name) $ M.elems $ e^.indices) ++ "]"

csched_sum :: EventId -> EventMerging' -> M ()
csched_sum lbl e = do
        -- unless (sch == def) $ 
        section kw $ do
            when show_removals $
                local (const True)
                    $ put_all_expr_with (makeRef %= isDefault) lbl del_sch
            put_all_expr_with (makeRef %= isDefault) lbl sch
    where
        isDefault f eid lbl
            | lbl == "default" = return $ format "(\\ref{{0}}/default)" (eid :: EventId)
            | otherwise        = f eid lbl
        kw = "\\textbf{during}"    
        sch = M.toList $ e^.new.coarse_sched --coarse $ new_sched e
        del_sch = concatMap (fmap M.toList $ view $ deleted.coarse_sched) $ e^.evt_pairs.to NE.toList
        -- def = M.singleton (label "default") zfalse

fsched_sum :: EventId -> EventMerging' -> M ()
fsched_sum lbl e = section kw $ do
        when show_removals $
            local (const True)
                $ put_all_expr lbl del_sch
        put_all_expr lbl xs
    where
        kw = "\\textbf{upon}"
        xs = e^.new' fine_sched -- fine $ new_sched e
        del_sch = concatMap (fmap M.toList $ view $ deleted.fine_sched) $ e^.evt_pairs.to NE.toList -- fine $ deleted_sched e

param_sum :: EventMerging' -> M ()
param_sum e
    | M.null $ e^.params  = return ()
    | otherwise           = do
        tell ["\\textbf{any} " 
            ++ intercalate "," (L.map (view name) $ M.elems $ e^.params)]

guard_sum :: EventId -> EventMerging' -> M ()
guard_sum lbl e = section kw $ do
        when show_removals $
            local (const True)
                $ put_all_expr lbl $ e^.deleted' raw_guards -- deleted_guard e
        put_all_expr lbl $ e^.new' raw_guards -- new_guard e
    where
        kw = "\\textbf{when}"

act_sum :: EventId -> EventMerging' -> M ()
act_sum lbl e = section kw $ do
        when show_removals $
            local (const True)
                $ put_all_expr' put_assign lbl $ e^.deleted' actions -- del_acts e
        put_all_expr' put_assign lbl $ M.toList $ e^.actions
    where 
        kw = "\\textbf{begin}"
        put_assign (Assign v e) = do
            xs <- get_string' e
            return $ format "{0} \\bcmeq {1}" (v^.name :: String) xs
        put_assign (BcmSuchThat vs e) = do
            xs <- get_string' e
            return $ format "{0} \\bcmsuch {1}" (intercalate "," $ L.map (view name) vs :: String) xs
        put_assign (BcmIn v e) = do
            xs <- get_string' e
            return $ format "{0} \\bcmin {1}" (v^.name :: String) xs

