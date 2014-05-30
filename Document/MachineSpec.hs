{-# LANGUAGE TemplateHaskell #-}
module Document.MachineSpec where
    
    -- Modules
import Document.Machine

import Latex.Parser

import Logic.Classes
import Logic.Const
import Logic.Expr
import Logic.Label
import Logic.Type

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.SetTheory

import UnitB.AST

    -- Libraries
import Control.Monad

import qualified Data.Map as M
import           Data.Maybe
import qualified Data.List as L

import Test.QuickCheck hiding (label)

import Utilities.Format
import Utilities.Syntactic

prop_parseOk :: CorrectMachineInput -> Bool
prop_parseOk (CorrectMachineInput mch tex) = 
        (M.elems . machines) `liftM` (all_machines tex) == Right [mch]

data CorrectMachineInput = CorrectMachineInput Machine [LatexDoc]


instance Arbitrary CorrectMachineInput where
    arbitrary = do
        m   <- arbitrary
        tex <- latex_of m
        return $ CorrectMachineInput m tex

perm :: Int -> Gen [Int]
perm n = permute [0..n-1]

permute :: [a] -> Gen [a]
permute xs = permute_aux (length xs) xs

permute_aux :: Int -> [a] -> Gen [a]
permute_aux 0 _  = return []
permute_aux n xs = sized $ \size -> do
        let s_size = round (sqrt $ fromIntegral size) `max` 2
            buck   = (n `div` s_size) `max` 1
        i  <- choose (0,n-1)
        let ys = drop i xs ++ take i xs
            z = take buck ys
        zs <- permute_aux (n-1) (drop buck ys)
        return $ z ++ zs


latex_of :: Machine -> Gen [LatexDoc]
latex_of m = do
        let m_name = Bracket True li 
                           [ Text [TextBlock (show $ _name m) li] ] 
                           li
            show_t t = M.findWithDefault "<unknown>" t type_map
            show_e v@(Word _) = show v
            show_e (FunApp f xs)
                    | name f == "+" = format "{0} + {1}" (show_e x) (as_sum y)
                    | name f == "=" = format "{0} = {1}" (show_e x) (show_e y)
                    | name f == "<=" = format "{0} \\le {1}" (show_e x) (show_e y)
                    | name f == "elem" = format "{0} \\in {1}" (as_sum x) (show_e y)
                    | otherwise = "<unknown function: " ++ show (name f) ++ ">"
                where
                    x = xs !! 0
                    y = xs !! 1
            show_e _ = "<unknown expression>"
            as_sum x@(FunApp f _)
                    | name f == "+" = format "({0})" (show_e x)
                    | otherwise     = show_e x
            as_sum x = show_e x
            type_map = M.fromList 
                        [ (int, "\\Int")
                        , (bool, "\\Bool")
                        , (set_type int, "\\set[\\Int]")
                        , (fun_type int int, "\\Int \\pfun \\Int")
                        ]
            cmd n args = Text [Command n li] : concatMap farg args
            farg x = [ Bracket True li [ Text [TextBlock x li]
                                    ] li, blank ]
            var_decl (Var n t) = cmd "\\variable" [(n ++ " : " ++ show_t t)]
            decls = map var_decl $ M.elems $ variables m
            imp_stat xs = cmd "\\with" [xs]
            inv_decl (lbl,xs) = cmd "\\invariant" [show lbl, show_e xs]
            invs        = map inv_decl $ M.toList $ inv $ props m
            imports = map imp_stat $ filter (/= "basic") 
                        $ M.keys $ extends $ theory m
        content <- concat `liftM` permute (decls ++ imports ++ invs)
        return [ Env "machine" li 
                       ( [ m_name, blank ] ++ content)
                       li ]
    where
        li = LI "" 0 0
        blank = Text [Blank "\n" li]

instance Arbitrary Machine where
    arbitrary = do
            nvar  <- choose (0,5)
            types <- L.sort `liftM` vectorOf nvar 
                    (elements [int,bool
                        ,set_type int
                        ,fun_type int int
                        ])
            let vars = map (uncurry $ Var . (:[])) $ zip ['a'..'z'] types
                mch = empty_machine "m0"
                inv_lbl = map (\x -> label $ "inv" ++ show x) [0..]
            ninv <- choose (0,5)
            inv  <- catMaybes `liftM` replicateM ninv 
                    (resize 4 $ expr_type (symbol_table vars) bool)
            return $ (empty_machine "m0")
                { theory = (theory mch) { extends = M.fromList 
                        [ ("sets", set_theory) 
                        , ("functions", function_theory) 
                        , ("arithmetic", arithmetic)
                        , ("basic", basic_theory)] }
                , variables = symbol_table vars
                , props = empty_property_set
                        { inv = M.fromList $ zip inv_lbl inv } }

expr_type :: (M.Map String Var) -> Type -> Gen (Maybe Expr)
expr_type vars t = sized $ \n ->do
        if n == 0 then 
            choose_var t
        else do
            oneof 
                [ choose_var t
                , choose_expr t
                ]
    where
        t_map = M.fromListWith (++) $ map f $ M.elems vars
        f v@(Var _ t) = (t,[v])
        choose_var t = 
            maybe
                (return Nothing)
                (((Just . Word) `liftM`) . elements)
                $ M.lookup t t_map
        fun_map = M.fromList
            [ (int, 
                [ (from_list zplus, [int,int])])
            , (bool, 
                [ (from_list zeq, [int,int]) 
                , (from_list zle, [int,int])
                , (from_list zelem', [int, set_type int] )])
            ]
        zelem' e0 e1 = either undefined id $ zelem (Right e0) (Right e1)
        choose_expr t = sized $ \n -> do
            case M.lookup t fun_map of
                Just xs -> do
                    (f,ts) <- elements xs
                    es <- forM ts $ resize (n-1) . expr_type vars
                    if (all isJust es) then
                        return $ Just $ f $ catMaybes es
                    else 
                        resize (n-1) $ expr_type vars t
                Nothing -> return Nothing
        --     if t == int then

        --     else if t == bool then

            -- else 

instance Show CorrectMachineInput where
    show (CorrectMachineInput _ tex) = unlines
            [ "" -- show m
            , concatMap flatten tex]

run_spec :: IO Bool
run_spec = $quickCheckAll

main :: IO ()
main = do
        xs <- sample' arbitrary
        let (CorrectMachineInput mch tex) = head 
                $ filter (not . prop_parseOk) xs
            mch' = (M.elems . machines) `liftM` (all_machines tex)
        writeFile "actual.txt" (show mch')
        writeFile "expect.txt" (show [mch])
