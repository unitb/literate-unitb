{-# LANGUAGE OverloadedStrings #-}
module Documentation.Test where

    -- 
    -- Modules
    --
import Document.Tests.Suite as S

import Documentation.SummaryGen

    --
    -- Libraries
    -- 
import Control.Lens
import Control.Precondition

import Data.Map as M
import Data.Map.Syntax

import System.IO.FileSystem

import Test.UnitTest

import Utilities.Syntactic

test_case :: TestCase
test_case = test_cases 
        "Documentation generation" 
        [ aCase "m2, event m1:moveout" case0 result0
        , aCase "m3, event m1:moveout" case1 result1
        , aCase "safety properties of m2" case2 result2
        , aCase "progress properties of m2" case3 result3
        , aCase "File structure" case4 result4
        , stringCase "Root machine" case5 result5
        , aCase "definitions of m2" case6 result6
        , aCase "assumptions of m2" case7 result7
        ]

result0 :: String
result0 = unlines
    [ "\\noindent \\ref{m1:moveout} $[t]$ \\textbf{event}"
    , "\\begin{block}"
    , "  \\item   \\textbf{refines}"
    , "  \\begin{block}"
    , "    \\item   \\ref{m1:moveout}"
    , "  \\end{block}"
    , "  \\item   \\textbf{during}"
    , "  \\begin{block}"
    , "    \\item[ ]{$t \\in in \\land loc.t \\in plf$} %"
    , "    %\\eqref{m1:moveoutc1}"
    , "  \\end{block}"
    , "  \\item   \\textbf{upon}"
    , "  \\begin{block}"
    , "    \\item[ ]{$\\neg ext \\in \\ran.loc$} %"
    , "    %\\eqref{m1:moveoutmo:f0}"
    , "  \\end{block}"
    , "  \\item   \\textbf{when}"
    , "  \\begin{block}"
    , "    \\item[ ]{$t \\in in$} %"
    , "    %\\eqref{m1:moveoutmo:g1}"
    , "    \\item[ ]{$loc.t \\in plf$} %"
    , "    %\\eqref{m1:moveoutmo:g2}"
    , "    \\item[ ]{$\\neg ext \\in \\ran.loc$} %"
    , "    %\\eqref{m1:moveoutmo:g3}"
    , "  \\end{block}"
    , "  \\item   \\textbf{begin}"
    , "  \\begin{block}"
    , "    \\item[ ]{$loc \\bcmsuch loc' = loc \\1 | t \\fun ext$} %"
    , "    %\\eqref{m1:moveouta2}"
    , "  \\end{block}"
    , "  \\item   \\textbf{end} \\\\"
    , "\\end{block}"
    ]

case0 :: IO String
case0 = makeReport $ do
    m <- parse_machine' path0 2
    let lbl = "m1:moveout"
    evt <- S.lookup lbl $ nonSkipUpwards m
    return $ getListing $
            event_summary' m lbl evt

path0 :: FilePath
path0 = [path|Tests/train-station-set.tex|]

result1 :: String
result1 = unlines
    [ "\\noindent \\ref{m1:moveout} $[t]$ \\textbf{event}"
    , "\\begin{block}"
    , "  \\item   \\textbf{refines}"
    , "  \\begin{block}"
    , "    \\item   \\ref{m1:moveout}"
    , "  \\end{block}"
    , "  \\item   \\textbf{during}"
    , "  \\begin{block}"
    , "    \\item[ ]{$t \\in in \\land loc.t \\in plf$} %"
    , "    %\\eqref{m1:moveoutc1}"
    , "    \\item[ ]{$loc.t \\in osgn$} %"
    , "    %\\eqref{m1:moveoutm3:mo:sch0}"
    , "  \\end{block}"
    , "  \\item   \\textbf{upon}"
    , "  \\begin{block}"
    , "    \\item[ ]\\sout{$\\neg ext \\in \\ran.loc$} %"
    , "    %\\eqref{m1:moveoutmo:f0}"
    , "  \\end{block}"
    , "  \\item   \\textbf{when}"
    , "  \\begin{block}"
    , "    \\item[ ]\\sout{$\\neg ext \\in \\ran.loc$} %"
    , "    %\\eqref{m1:moveoutmo:g3}"
    , "  \\end{block}"
    , "  \\begin{block}"
    , "    \\item[ ]{$loc.t \\in osgn$} %"
    , "    %\\eqref{m1:moveoutm3:mo:grd0}"
    , "    \\item[ ]{$t \\in in$} %"
    , "    %\\eqref{m1:moveoutmo:g1}"
    , "    \\item[ ]{$loc.t \\in plf$} %"
    , "    %\\eqref{m1:moveoutmo:g2}"
    , "  \\end{block}"
    , "  \\item   \\textbf{begin}"
    , "  \\begin{block}"
    , "    \\item[ ]{$loc \\bcmsuch loc' = loc \\1 | t \\fun ext$} %"
    , "    %\\eqref{m1:moveouta2}"
    , "    \\item[ ]{$isgn,osgn \\bcmsuch isgn' = isgn$} %"
    , "    %\\eqref{m1:moveoutm3:mo:act0}"
    , "    \\item[ ]{$isgn,osgn \\bcmsuch osgn'  \\2 = osgn  %"
    , "  \t\\setminus \\{ loc.t \\}$} %"
    , "    %\\eqref{m1:moveoutm3:mo:act1}"
    , "  \\end{block}"
    , "  \\item   \\textbf{end} \\\\"
    , "\\end{block}"
    ]

case1 :: IO String
case1 = makeReport $ do
    m <- parse_machine' path0 3
    let lbl = "m1:moveout"
    evt <- S.lookup lbl $ nonSkipUpwards m
    return $ getListing $
            event_summary' m lbl evt

result2 :: String
result2 = unlines
    [ "\\textbf{safety}"
    , "\\begin{block}"
    , "  \\item[ \\eqref{m2:saf1} ]{$t \\in in \\land loc.t = ext \\textbf{\\quad unless \\quad} \\neg ext \\in \\ran. loc$} %"
    , "  \\item[ \\eqref{m2:saf2} ]{$t \\in in \\land b \\in plf \\1\\land  loc.t = b \\textbf{\\quad unless \\quad} b \\in plf \\1\\land \\qforall{t}{ t \\in in }{ \\neg loc.t = b }$} %"
    , "\\end{block}"
    ]

case2 :: IO String
case2 = makeReport $ do
    p <- view' props <$> parse_machine' path0 2
    return $ getListing $
        safety_sum p

result3 :: String
result3 = unlines
    [ "\\textbf{progress}"
    , "\\begin{block}"
    , "  \\item[ \\eqref{m2:prog0} ]{$\\true \\quad \\mapsto\\quad \\neg plf \\subseteq \\ran.loc$} %"
    , "  \\item[ \\eqref{m2:prog1} ]{$\\true \\quad \\mapsto\\quad \\neg ext \\in \\ran.loc$} %"
    , "  \\item[ \\eqref{m2:prog2} ]{$ext \\in \\ran. loc \\quad \\mapsto\\quad \\neg ext \\in \\ran. loc$} %"
    , "  \\item[ \\eqref{m2:prog3} ]{$t \\in in \\land loc.t = ext \\quad \\mapsto\\quad \\neg ext \\in \\ran. loc$} %"
    , "  \\item[ \\eqref{m2:prog4} ]{$plf \\subseteq \\ran.loc \\!\\! \\quad \\mapsto\\quad \\!\\! \\neg ~ plf \\subseteq \\ran.loc$} %"
    , "  \\item[ \\eqref{m2:prog5} ]{$\\qexists{b}{b \\in plf}{ b \\in \\ran.loc } \\quad \\mapsto\\quad \\qexists{b}{}{ b \\in plf \\1\\land \\neg b \\in \\ran.loc }$} %"
    , "  \\item[ \\eqref{m2:prog6} ]{$\\qexists{t}{t \\in in}{ b \\in plf \\1\\land  loc.t = b } \\quad \\mapsto\\quad b \\in plf \\land \\neg b \\in \\ran.loc$} %"
    , "  \\item[ \\eqref{m2:prog7} ]{$t \\in in \\land b \\in plf \\1\\land  loc.t = b \\quad \\mapsto\\quad b \\in plf \\land \\neg b \\in \\ran.loc$} %"
    , "\\end{block}"
    ]

case3 :: IO String
case3 = makeReport $ do
    m <- parse_machine' path0 2
    return $ getListing $
        liveness_sum m

result4 :: Either String (Map FilePath Bool)
result4 = Right $ fromRight' $ runMap $ do
        "." ## False
        "/" ## False
        "dir" ## False 
        "dir/file" ## False 
        "dir/file/m0_m0-enter.tex"   ## True
        "dir/file/m0_m0-leave.tex"   ## True 
        "dir/file/m1_m0-enter.tex"   ## True
        "dir/file/m1_m0-leave.tex"   ## True 
        "dir/file/m1_m1-moveout.tex" ## True
        "dir/file/m1_m1-movein.tex"  ## True
        "dir/file/m2_m0-enter.tex"   ## True
        "dir/file/m2_m0-leave.tex"   ## True 
        "dir/file/m2_m1-moveout.tex" ## True
        "dir/file/m2_m1-movein.tex"  ## True
        "dir/file/m3_m0-enter.tex"   ## True
        "dir/file/m3_m0-leave.tex"   ## True 
        "dir/file/m3_m1-moveout.tex" ## True
        "dir/file/m3_m1-movein.tex"  ## True
        "dir/file/m3_m3-ctr-plf.tex" ## True
        "dir/file/machine_m0.tex" ## True
        "dir/file/machine_m0_co.tex"    ## True
        "dir/file/machine_m0_asm.tex"   ## True
        "dir/file/machine_m0_def.tex"   ## True
        "dir/file/machine_m0_inv.tex"   ## True
        "dir/file/machine_m0_prog.tex"  ## True
        "dir/file/machine_m0_props.tex" ## True
        "dir/file/machine_m0_saf.tex"   ## True
        "dir/file/machine_m0_thm.tex"   ## True
        "dir/file/machine_m0_trans.tex" ## True
        "dir/file/machine_m1.tex" ## True
        "dir/file/machine_m1_co.tex"    ## True
        "dir/file/machine_m1_asm.tex"   ## True
        "dir/file/machine_m1_def.tex"   ## True
        "dir/file/machine_m1_inv.tex"   ## True
        "dir/file/machine_m1_prog.tex"  ## True
        "dir/file/machine_m1_props.tex" ## True
        "dir/file/machine_m1_saf.tex"   ## True
        "dir/file/machine_m1_thm.tex"   ## True
        "dir/file/machine_m1_trans.tex" ## True
        "dir/file/machine_m2.tex" ## True
        "dir/file/machine_m2_co.tex"    ## True
        "dir/file/machine_m2_asm.tex"   ## True
        "dir/file/machine_m2_def.tex"   ## True
        "dir/file/machine_m2_inv.tex"   ## True
        "dir/file/machine_m2_prog.tex"  ## True
        "dir/file/machine_m2_props.tex" ## True
        "dir/file/machine_m2_saf.tex"   ## True
        "dir/file/machine_m2_thm.tex"   ## True
        "dir/file/machine_m2_trans.tex" ## True
        "dir/file/machine_m3.tex" ## True
        "dir/file/machine_m3_co.tex"    ## True
        "dir/file/machine_m3_asm.tex"   ## True
        "dir/file/machine_m3_def.tex"   ## True
        "dir/file/machine_m3_inv.tex"   ## True
        "dir/file/machine_m3_prog.tex"  ## True
        "dir/file/machine_m3_props.tex" ## True
        "dir/file/machine_m3_saf.tex"   ## True
        "dir/file/machine_m3_thm.tex"   ## True
        "dir/file/machine_m3_trans.tex" ## True

case4 :: IO (Either String (Map FilePath Bool))
case4 = runEitherT $ do
    s <- get_system path0
    return $ M.map isJust $ view' files $ execMockFileSystem 
        $ produce_summaries "dir/file.ext" s

case5 :: IO String
case5 = makeReport $ do
    s <- get_system' path0
    let fs = execMockFileSystem $ produce_summaries "dir/file.ext" s
    return $ fromMaybe "documentation file not found" $ (fs^.content')^?files.ix "dir/file/machine_m3.tex".traverse

result5 :: String
result5 = unlines 
    [ "%!TEX root=../file.ext"
    , "\\begin{block}"
    , "  \\item   \\textbf{machine} m3"
    , "  \\item   \\textbf{refines} m2"
    , "  \\item   \\textbf{sets}"
    , "  \\begin{block}"
    , "    \\item   $\\Blk$"
    , "    \\item   $\\Train$"
    , "  \\end{block}"
    , "  \\item   \\textbf{constants}"
    , "  \\begin{block}"
    , "    \\item   $ent \\in \\Blk$"
    , "    \\item   $ext \\in \\Blk$"
    , "    \\item   $plf \\subseteq \\Blk$"
    , "  \\end{block}"
    , "  \\item   \\input{file/machine_m3_asm}"
    , "  \\item   \\textbf{variables}"
    , "  \\begin{block}"
    , "    \\item   $in \\subseteq \\Train$"
    , "    \\item   $loc \\in \\Train \\pfun \\Blk$"
    , "    \\item   $isgn \\in \\textbf{Bool}$\\quad(new)"
    , "    \\item   $osgn \\subseteq \\Blk$\\quad(new)"
    , "  \\end{block}"
    , "  \\item   \\input{file/machine_m3_inv}"
    , "  \\item   \\input{file/machine_m3_prog}"
    , "  \\item   \\input{file/machine_m3_saf}"
    , "  \\item   \\input{file/machine_m3_trans}"
    , "  \\item   \\textbf{initialization}"
    , "  \\begin{block}"
    , "    \\item[ ]{$loc \\, = \\emptyfun$} %"
    , "    %\\eqref{in0}"
    , "    \\item[ ]{$in = \\emptyset$} %"
    , "    %\\eqref{in1}"
    , "    \\item[ ]{$osgn = \\emptyset$} %"
    , "    %\\eqref{m3:init0}"
    , "    \\item[ ]{$isgn = \\false$} %"
    , "    %\\eqref{m3:init1}"
    , "  \\end{block}"
    , "  \\textbf{events}"
    , "  \\begin{block}"
    , "    \\item   \\input{file/m3_m0-enter}"
    , "    \\item   \\input{file/m3_m0-leave}"
    , "    \\item   \\input{file/m3_m1-movein}"
    , "    \\item   \\input{file/m3_m1-moveout}"
    , "    \\item   \\input{file/m3_m3-ctr-plf}"
    , "  \\end{block}"
    , "  \\item   \\textbf{end} \\\\"
    , "\\end{block}"
    ]

path6 :: FilePath
path6 = [path|Tests/lock-free deque/main12.tex|]

result6 :: String
result6 = unlines
    [ "\\textbf{definitions}"
    , "\\begin{block}"
    , "  \\item[] {$Req \\3\\triangleq [ 'req : \\REQ ]$} %"
    , "\\end{block}"
    ]

case6 :: IO String
case6 = makeReport $ do
    m <- parse_machine' path6 2
    return $ getListing $
        defs_sum m

result7 :: String
result7 = unlines
    [ "\\textbf{assumptions}"
    , "\\begin{block}"
    , "  \\item[ \\eqref{asm0} ]{$\\neg ext \\in plf \\1\\land \\neg ext = ent$} %"
    , "  \\item[ \\eqref{asm1} ]{$\\qforall{b}{}{ b \\in \\Blk \\2\\equiv b \\in plf \\1\\lor b = ent \\1\\lor b = ext }$} %"
    , "  \\item[ \\eqref{asm2} ]{$\\qexists{b}{}{b \\in plf}$} %"
    , "  \\item[ \\eqref{asm3} ]{$\\neg ent \\in plf$} %"
    , "  \\item[ \\eqref{asm7} ]{$(\\{ ext \\} \\bunion plf = \\compl \\{ent\\}) \\land (\\{ ent \\} \\bunion plf = \\compl \\{ext\\}) \\land \\{ ext, ent \\} = \\compl plf$} %"
    , "\\end{block}"
    ]

case7 :: IO String
case7 = makeReport $ do
    m <- parse_machine' path0 2
    return $ getListing $
        asm_sum m
