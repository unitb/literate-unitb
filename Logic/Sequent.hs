{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Logic.Sequent where

    -- Modules
import Logic.Expr
import Logic.Label
import Logic.Const
import Logic.Type

    -- Libraries
import Data.Char
import Data.List
import Data.Map hiding ( map )

import GHC.Generics

import Utilities.Format

type Sequent = AbsSequent GenericType

type FOSequent = AbsSequent FOType

data AbsSequent t = Sequent (AbsContext t) [AbsExpr t] (Map Label (AbsExpr t)) (AbsExpr t)
    deriving (Eq, Generic)

instance Show Sequent where
    show (Sequent (Context ss vs fs ds _) as hs g) =
            unlines (
                   map (" " ++)
                (  ["sort: " ++ intercalate ", " (map f $ toList ss)]
                ++ (map show $ elems fs)
                ++ (map show $ elems ds)
                ++ (map show $ elems vs)
                ++ map show (as ++ elems hs))
                ++ ["|----"," " ++ show g] )
        where
            f (_, IntSort) = ""
            f (_, BoolSort) = ""
            f (_, RealSort) = ""
            f (x, Datatype args n _) = f (x, Sort n n $ length args)
            f (x, DefSort y z xs _)  = f (x, Sort y z $ length xs)
            f (_, Sort _ z 0) = z
            f (_, Sort _ z n) = format "{0} [{1}]" z (intersperse ',' $ map chr $ take n [ord 'a' ..]) 

entailment :: Sequent -> Sequent -> (Sequent,Sequent)
entailment  
    (Sequent (Context srt0 cons0 fun0 def0 dum0) xs0 hs0 xp0) 
    (Sequent (Context srt1 cons1 fun1 def1 dum1) xs1 hs1 xp1) = 
            (po0,po1)
    where
        po0 = Sequent 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            []
            empty
            $ xp0 `zimplies` xp1 
        po1 = Sequent 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            xs1
            hs1
            (zall $ xs0 ++ elems hs0)
