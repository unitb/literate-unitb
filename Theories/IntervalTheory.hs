{-# LANGUAGE RecordWildCards, TemplateHaskell #-}
module Theories.IntervalTheory where

    -- Modules
import Logic.Expr
import Logic.Operator
import Logic.Theory

import Theories.Arithmetic
import Theories.SetTheory

    -- Libraries
import Control.Lens

import qualified Data.Map as M

    -- arithmetic

type Rel = ExprP -> ExprP -> ExprP

zbetween :: Rel -> Rel -> ExprP -> ExprP -> ExprP -> ExprP
zbetween r1 r2 mx my mz = 
      (mx `r1` my) `mzand` (my `r2` mz)

interval_fun :: Fun
interval_fun    = mk_fun [] "interval"  [int,int] $ set_type int
interval_l_fun :: Fun
interval_l_fun  = mk_fun [] "intervalL" [int,int] $ set_type int
interval_r_fun :: Fun
interval_r_fun  = mk_fun [] "intervalR" [int,int] $ set_type int
interval_lr_fun :: Fun
interval_lr_fun = mk_fun [] "intervalLR" [int,int] $ set_type int

zinterval :: Rel
zinterval = typ_fun2 interval_fun
zinterval_l :: Rel
zinterval_l = typ_fun2 interval_l_fun
zinterval_r :: Rel
zinterval_r = typ_fun2 interval_r_fun
zinterval_lr :: Rel
zinterval_lr = typ_fun2 interval_lr_fun

interval :: Command
interval = Command "\\interval" "interval" 2 $ from_list zinterval
interval_l :: Command
interval_l = Command "\\intervalL" "intervalL" 2 $ from_list zinterval_l
interval_r :: Command
interval_r = Command "\\intervalR" "intervalR" 2 $ from_list zinterval_r
interval_lr :: Command
interval_lr = Command "\\intervalLR" "intervalLR" 2 $ from_list zinterval_lr

between :: Command
between = Command "\\between" "between" 3 $ from_list $ zbetween mzle mzle
between_l :: Command
between_l = Command "\\betweenL" "betweenL" 3 $ from_list $ zbetween mzless mzle
between_r :: Command
between_r = Command "\\betweenR" "betweenR" 3 $ from_list $ zbetween mzle mzless
between_lr :: Command
between_lr = Command "\\betweenLR" "betweenLR" 3 $ from_list $ zbetween mzless mzless

interval_theory :: Theory
interval_theory = empty_theory 
        { _extends = M.fromList 
            [ ("set",set_theory)
            , ("arithmetic",arithmetic) ]
        , _funs = symbol_table
            [ interval_r_fun, interval_l_fun
            , interval_lr_fun, interval_fun ]
        , _fact = M.mapKeys label $ M.fromList
            [ ("axm0", ($typeCheck) $ mzforall [x_decl,m_decl,n_decl] mztrue $
                                (x `zelem` zinterval m n) 
                        `mzeq`  (zbetween mzle mzle m x n))
            , ("axm1", ($typeCheck) $ mzforall [x_decl,m_decl,n_decl] mztrue $
                                (x `zelem` zinterval_r m n) 
                        `mzeq`  (zbetween mzle mzless m x n))
            , ("axm2", ($typeCheck) $ mzforall [x_decl,m_decl,n_decl] mztrue $
                                (x `zelem` zinterval_l m n) 
                        `mzeq`  (zbetween mzless mzle m x n))
            , ("axm3", ($typeCheck) $ mzforall [x_decl,m_decl,n_decl] mztrue $
                                (x `zelem` zinterval_l m n) 
                        `mzeq`  (zbetween mzless mzle m x n))
            , ("axm4", ($typeCheck) $ mzforall [m_decl] mztrue $
                                zinterval_r m m
                        `mzeq`  zempty_set)
            , ("axm5", ($typeCheck) $ mzforall [m_decl] mztrue $
                                zinterval_l m m
                        `mzeq`  zempty_set)
            , ("axm6", ($typeCheck) $ mzforall [m_decl] mztrue $
                                zinterval_r m (m + z1)
                        `mzeq`  zmk_set m)
            , ("axm7", ($typeCheck) $ mzforall [m_decl] mztrue $
                                zinterval_l (m - z1) m
                        `mzeq`  zmk_set m)
            , ("axm8", ($typeCheck) $ mzforall [m_decl,n_decl,p_decl] 
                            (zbetween mzle mzle m n p) $
                                (zinterval_r m n `zunion` zinterval_r n p)
                        `mzeq`  (zinterval_r m p))
            , ("axm9", ($typeCheck) $ mzforall [m_decl,n_decl,p_decl] 
                            (zbetween mzle mzle m n p) $
                                (zinterval_l m n `zunion` zinterval_l n p)
                        `mzeq`  (zinterval_l m p))
            , ("axm10", ($typeCheck) $ mzforall [m_decl,n_decl] 
                            (mzle m n) $
                                (zinterval_r m n `zunion` zmk_set n)
                        `mzeq`  (zinterval_r m (n+z1)))
            , ("axm11", ($typeCheck) $ mzforall [m_decl,n_decl] 
                            (mzle m n) $
                                (zinterval_l m n `zunion` zmk_set (n + z1))
                        `mzeq`  (zinterval_l m (n+z1)))
            , ("axm12", ($typeCheck) $ mzforall [m_decl,n_decl] 
                            (mzle m n) $
                                (zmk_set (m - z1) `zunion` zinterval_r m n)
                        `mzeq`  (zinterval_r (m - z1) n))
            , ("axm13", ($typeCheck) $ mzforall [m_decl,n_decl] 
                            (mzle m n) $
                                (zmk_set m `zunion` zinterval_l m n)
                        `mzeq`  (zinterval_l (m - z1) n))
            ]
        , _notation = interval_notation }
    where
        (x,x_decl) = var "x" int
        (m,m_decl) = var "m" int
        (n,n_decl) = var "n" int
        (p,p_decl) = var "p" int
        (+) = mzplus
        (-) = mzminus
        z1 = mzint 1

interval_notation :: Notation
interval_notation = empty_notation
    & commands   .~ [ between, between_l, between_r, between_lr
                    , interval, interval_l, interval_r, interval_lr ] 
          