{-# LANGUAGE OverloadedStrings #-}
module Documentation.Test where

    -- 
    -- Modules
    --
import Document.Tests.Suite

import Documentation.SummaryGen

import UnitB.AST

    --
    -- Libraries
    -- 
import Control.Monad
import Control.Monad.Trans.Either

import Data.Map

import Tests.UnitTest

test_case :: TestCase
test_case = test_cases 
        "Documentation generation" 
        [ Case "m2, event m1:moveout" case0 result0
        , Case "m3, event m1:moveout" case1 result1
        , Case "safety properties of m2" case2 result2
        , Case "progress properties of m2" case3 result3
        ]

result0 :: String
result0 = unlines
    [ "\\noindent \\ref{m1:moveout} [t] \\textbf{event}"
    , "\\begin{block}"
    , "  \\item   \\textbf{during}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutc1} ]{$t \\in in \\land loc.t \\in plf $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{upon}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutmo:f0} ]{$\\neg ext \\in \\ran. loc $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{when}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutmo:g1} ]{$t \\in in $} %"
    , "  \\item[ \\eqref{m1:moveoutmo:g2} ]{$loc.t \\in plf $} %"
    , "  \\item[ \\eqref{m1:moveoutmo:g3} ]{$\\neg ext \\in \\ran. loc $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{begin}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveouta2} ]{$loc \\bcmsuch loc' = loc \\1 | t \\fun ext $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{end} \\\\"
    , "\\end{block}"
    ]

case0 :: IO String
case0 = liftM (either id id) $ runEitherT $ do
    s <- get_system path0
    let ms  = machines s
        lbl = "m1:moveout"
        m   = ms ! "m2"
    return $ getListing $ 
            event_summary' m lbl (nonSkipUpwards m ! lbl)
            -- ) (expr_store s,"")

path0 :: String
path0 = "Tests/train-station-set.tex"

result1 :: String
result1 = unlines
    [ "\\noindent \\ref{m1:moveout} [t] \\textbf{event}"
    , "\\begin{block}"
    , "  \\item   \\textbf{during}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutc1} ]{$t \\in in \\land loc.t \\in plf $} %"
    , "  \\item[ \\eqref{m1:moveoutm3:mo:sch0} ]{$loc.t \\in osgn $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{upon}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutmo:f0} ]\\sout{$\\neg ext \\in \\ran. loc $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{when}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutmo:g3} ]\\sout{$\\neg ext \\in \\ran. loc $} %"
    , "  \\end{block}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveoutm3:mo:grd0} ]{$loc.t \\in osgn $} %"
    , "  \\item[ \\eqref{m1:moveoutmo:g1} ]{$t \\in in $} %"
    , "  \\item[ \\eqref{m1:moveoutmo:g2} ]{$loc.t \\in plf $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{begin}"
    , "  \\begin{block}"
    , "  \\item[ \\eqref{m1:moveouta2} ]{$loc \\bcmsuch loc' = loc \\1 | t \\fun ext $} %"
    , "  \\item[ \\eqref{m1:moveoutm3:mo:act0} ]{$isgn,osgn \\bcmsuch isgn' = isgn$} %"
    , "  \\item[ \\eqref{m1:moveoutm3:mo:act1} ]{$isgn,osgn \\bcmsuch osgn'  \\2 = osgn  %"
    , "  \t\\setminus \\{ loc.t \\} $} %"
    , "  \\end{block}"
    , "  \\item   \\textbf{end} \\\\"
    , "\\end{block}"
    ]

case1 :: IO String
case1 = liftM (either id id) $ runEitherT $ do
    s <- get_system path0
    let ms  = machines s
        lbl = "m1:moveout"
        m   = ms ! "m3"
    return $ getListing $
            event_summary' m lbl (nonSkipUpwards m ! lbl)

result2 :: String
result2 = unlines
    [ "\\textbf{safety}"
    , "\\begin{block}"
    , "\\item[ \\eqref{m2:saf0} ]{$\\neg ~ plf \\subseteq \\ran.loc  \\textbf{\\quad unless \\quad} \\false\\qquad  \\text{(except \\ref{m1:movein})}$} %"
    , "\\item[ \\eqref{m2:saf1} ]{$t \\in in \\land loc.t = ext  \\textbf{\\quad unless \\quad} \\neg ext \\in \\ran. loc $} %"
    , "\\item[ \\eqref{m2:saf2} ]{$t \\in in \\land b \\in plf \\1\\land  loc.t = b  \\textbf{\\quad unless \\quad} b \\in plf \\1\\land \\qforall{t}{ t \\in in }{ \\neg loc.t = b } $} %"
    , "\\end{block}"
    ]

case2 :: IO String
case2 = liftM (either id id) $ runEitherT $ do
    s <- get_system path0
    let ms  = machines s
        m   = ms ! "m2"
        p   = m!.props
    return $ getListing $
        safety_sum p

result3 :: String
result3 = unlines
    [ "\\textbf{progress}"
    , "\\begin{block}"
    , "\\item[ \\eqref{m2:prog0} ]{$\\true \\quad \\mapsto\\quad \\neg ~ plf \\subseteq \\ran.loc $} %"
    , "\\item[ \\eqref{m2:prog1} ]{$\\true \\quad \\mapsto\\quad \\neg ext \\in \\ran. loc $} %"
    , "\\item[ \\eqref{m2:prog2} ]{$ext \\in \\ran. loc  \\quad \\mapsto\\quad \\neg ext \\in \\ran. loc $} %"
    , "\\item[ \\eqref{m2:prog3} ]{$t \\in in \\land loc.t = ext  \\quad \\mapsto\\quad \\neg ext \\in \\ran. loc $} %"
    , "\\item[ \\eqref{m2:prog4} ]{$plf \\subseteq \\ran.loc \\!\\! \\quad \\mapsto\\quad \\neg ~ plf \\subseteq \\ran.loc $} %"
    , "\\item[ \\eqref{m2:prog5} ]{$\\qexists{b}{b \\in plf}{ b \\in \\ran.loc } \\quad \\mapsto\\quad \\qexists{b}{}{ b \\in plf \\1\\land \\neg b \\in \\ran.loc } $} %"
    , "\\item[ \\eqref{m2:prog6} ]{$\\qexists{t}{t \\in in}{ b \\in plf \\1\\land  loc.t = b }  \\quad \\mapsto\\quad b \\in plf \\land \\neg b \\in \\ran.loc $} %"
    , "\\item[ \\eqref{m2:prog7} ]{$t \\in in \\land b \\in plf \\1\\land  loc.t = b  \\quad \\mapsto\\quad b \\in plf \\land \\neg b \\in \\ran.loc $} %"
    , "\\end{block}"
    ]

case3 :: IO String
case3 = liftM (either id id) $ runEitherT $ do
    s <- get_system path0
    let ms  = machines s
        m   = ms ! "m2"
    return $ getListing $
        liveness_sum m
