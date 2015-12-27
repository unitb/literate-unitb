{-# LANGUAGE RecordWildCards #-}
module Theories.Arithmetic where

    -- Modules
import Logic.Expr
import Logic.Expr.Const
import Logic.Operator
import Logic.Proof hiding (syntacticProp)
import Logic.Theory
import Logic.Theory.Monad

import Theories.SetTheory
import Theories.FunctionTheory

    -- Libraries
import Control.Arrow
import Control.Lens

import Data.List as L
import Data.Map

import Utilities.Lens

    -- arithmetic
power   :: BinOperator
mult    :: BinOperator
plus    :: BinOperator
minus   :: BinOperator
less    :: BinOperator
greater :: BinOperator
leq     :: BinOperator
geq     :: BinOperator

power   = make BinOperator "^" "^"           mzpow
mult    = make BinOperator "*" "\\cdot"      mztimes
plus    = make BinOperator "+" "+"           mzplus
minus   = make BinOperator "-" "-"           mzminus
less    = make BinOperator "<" "<"           mzless
greater = make BinOperator ">" ">"           (flip mzless)
leq     = make BinOperator "<=" "\\le"       mzle
geq     = make BinOperator ">=" "\\ge"       (flip mzle)

zsum :: [Var] -> ExprP -> ExprP -> ExprP
zsum = zquantifier qsum

zcard :: ExprP -> ExprP
zcard x = typ_fun2 sum_fun x (zconst $ mzint 1)

gT :: Type
gT = VARIABLE $ fromString'' "t"

arithmetic :: Theory
arithmetic = (empty_theory' "arithmetic") { 
        _extends = symbol_table [set_theory]
        , _types = symbol_table [IntSort,RealSort]
        , _funs = symbol_table 
            [ sum_fun ]
        , _theorySyntacticThm = empty_monotonicity
            { _associative  = fromList [(fromString'' "+",mzint 0)] 
            , _monotonicity = fromList $ L.map (first $ z3Name *** z3Name)
              [ (("=>","<="), Side (Just zge' )
                                   (Just zle'))
              , (("<=","+"), Independent zle')
              , (("<=","-"),  Side (Just zge') 
                                   (Just zle')) ] }
        , _fact = "arithmetic" `axioms` do
                $axiom $ 
                    asum zempty_set term `mzeq` mzint 0

                $axiom $ 
                    (mznot $ x `zelem` r) .=>
                         asum (r `zunion` zmk_set x) term  
                    .=. (asum r term .+ zselect term x)

                $axiom $ 
                    (r `zintersect` r' .=. zempty_set) .=>
                         asum (r `zunion` r') term 
                    .=. (asum r term .+ asum r' term)

                $axiom $ mzfinite r .=>
                    mzint 0 .<= zcard r

                $axiom $ 
                    zcard r .=. mzint 0  .==.  r .=. zempty_set

                $axiom $ 
                    zcard (zmk_set x) .=. mzint 1

                $axiom $
                         zcard r .=. mzint 1
                    .==. mzexists [x_decl] mztrue (r .=. zmk_set x)

                    -- dangerous!
                -- $axiom $ 
                --     mznot (x `zelem` r) .=>
                --          zcard (r `zunion` zmk_set x)
                --     .=.  zcard r .+ mzint 1

                $axiom $ 
                    r `zintersect` r' .=. zempty_set .=>
                         zcard (r `zunion` r')
                    .=.  zcard r .+ zcard r'            

            -- fromList $ L.map (first $ label . dec')
            -- [ ("0",axm1) 
            -- , ("1",axm2)
            -- , ("2",axm3)
            -- , ("3",axm4)
            -- -- , ("4",axm5)
            -- , ("5",axm6) 
            -- , ("6",axm7)
            -- , ("7",axm8)
            -- -- , ("8",axm9)
            -- -- , ("9",axm10)
            -- ]
        , _notation = arith }
    where
        zle' = Rel le_fun Direct
        zge' = Rel le_fun Flipped
        -- cast = zcast (set_type gT)
        asum = typ_fun2 sum_fun
        (term,_term_decl) = var "term" (array gT int)
        (r,_r_decl) = var "r" (set_type gT)
        (r',_r'_decl) = var "r0" (set_type gT)
        (x,x_decl) = var "x" gT
        


sum_fun :: Fun
sum_fun = mk_fun [gA] (fromString'' "qsum") [set_type gA, array gA int] int

qsum :: HOQuantifier
qsum = UDQuant sum_fun int (QTConst int) FiniteWD

arith :: Notation
arith = create $ do
   new_ops     .= L.map Right [power,mult,plus,leq,geq
                                ,less,greater,minus]
   prec .= [ L.map (L.map Right)
                     [ [apply]
                     , [power]
                     , [mult]
                     , [plus,minus]
                     , [mk_fun_op]
                     , [ equal,leq
                       , less
                       , geq,greater]]]
   left_assoc  .= [[mult],[plus]]
   right_assoc .= []
   relations   .= [equal,leq,geq,less,greater]
   chaining    .= 
          [ ((leq,leq),leq)
          , ((leq,less),less)
          , ((less,leq),less)
          , ((less,less),less)
          , ((geq,geq),geq)
          , ((geq,greater),greater)
          , ((greater,geq),greater)
          , ((greater,greater),greater) ] 
   commands .= [make Command "\\card" "card" 1 $ from_list zcard]
   quantifiers .= 
        [ (fromString'' "\\qsum"
          , qsum)]
          