{-# LANGUAGE TemplateHaskell #-}
module Document.MachineSpec where
    
    -- Modules
import Document.Machine

import Latex.Parser

import Logic.Expr
import Logic.Operator hiding (Command)

import Theories.Arithmetic
import Theories.FunctionTheory
import Theories.SetTheory

import UnitB.AST

    -- Libraries
import Control.Monad

import           Data.Either
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.List as L
import qualified Data.Set as S

import Test.QuickCheck hiding (label)

import           Utilities.Format
import qualified Utilities.Graph as G 
import           Utilities.Syntactic

prop_parseOk :: Property
prop_parseOk = forAll correct_machine $ f_prop_parseOk

f_prop_parseOk :: (Machine, Tex) -> Bool
f_prop_parseOk (mch,Tex tex) =
        (M.elems . machines) `liftM` (all_machines tex) == Right [mch]

prop_type_error :: Property
prop_type_error = forAll (liftM snd mch_with_type_error) f_prop_type_error

f_prop_type_error :: Tex -> Bool
f_prop_type_error (Tex tex) = either (all is_type_error) (const False) (all_machines tex) 

data MachineInput = MachineInput Machine [LatexDoc]

is_type_error :: Error -> Bool
is_type_error (Error msg _) = 
            "type error:" `L.isInfixOf` msg
        ||  "expected type:" `L.isInfixOf` msg

correct_machine :: Gen (Machine, Tex)
correct_machine = machine_input arbitrary

mch_with_type_error :: Gen (Machine, Tex)
mch_with_type_error = machine_input with_type_error

machine_input :: Gen Machine -> Gen (Machine, Tex)
machine_input cmd = do
        m   <- cmd
        tex <- latex_of m
        return (m,Tex tex)

-- instance Arbitrary MachineInput where
--     arbitrary = do
--         m   <- arbitrary
--         tex <- latex_of m
--         return $ CorrectMachineInput m tex

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
            root_op (FunApp f _) = find_op f
            root_op _ = Nothing
            find_op f = name f `M.lookup` m_ops 
            m_ops = M.fromList $ zip (map token xs) xs
                where
                    xs = new_ops $ all_notation m
            show_e v@(Word _) = show v
            show_e (FunApp f xs) 
                | length xs == 2 = format "{0} {1} {2}" 
                                    (show_left_sub_e op x)
                                    op_name
                                    (show_right_sub_e op y)
                | length xs == 1 = format "{0} {1}" 
                                    op_name
                                    (show_right_sub_e op x)
                | length xs == 0 = error $ format "show_e: not a binary or unary operator '{0}' {1}"
                                        (name f)
                                        (L.intercalate ", " $ map show xs)
                | otherwise      = show_e (FunApp f $ [head xs, FunApp f $ tail xs])
                where
                    x = xs !! 0
                    y = xs !! 1
                    op = maybe (Right plus) id $ find_op f
                    op_name = maybe unknown name $ find_op f
                    unknown = "<unknown function: " ++ show (name f) ++ ">"
            show_e (Const _ n _) = n
            show_e _ = "<unknown expression>"
            show_left_sub_e op e = maybe (show_e e) f $ root_op e
                where
                    g op' = struct (all_notation m) G.! (op',op)
                    f op'
                        | g op' == LeftAssoc = show_e e
                        | otherwise          = format "({0})" $ show_e e
            show_right_sub_e op e = maybe (show_e e) f $ root_op e
                where
                    g op' = struct (all_notation m) G.! (op,op')
                    f op'
                        | g op' == RightAssoc = show_e e
                        | otherwise           = format "({0})" $ show_e e
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

expressions :: Machine -> [Expr]
expressions m = M.elems $ inv $ props m

with_type_error :: Gen Machine
with_type_error = do
        suchThat (gen_machine True)
             (\m -> not $ L.null $ range m)
        -- (Var n t) <- elements $ range m
        -- t'        <- other_type t
        -- return m { variables = M.insert n (Var n t') $ variables m }
    where
        range m = M.elems vars `L.intersect` S.elems fv
            where
                vars  = variables m
                fv    = S.unions $ map used_var $ expressions m

choose_type :: Gen Type
choose_type = do
        elements [int,bool
                 ,set_type int
                 ,fun_type int int
                 ]

other_type :: Type -> Gen Type
other_type t = do
        elements $ L.delete t 
                 [int,bool
                 ,set_type int
                 ,fun_type int int
                 ]

data Tex = Tex { unTex :: [LatexDoc] }

instance Show Tex where
    show (Tex tex) = unlines
            [ "" -- show m
            , concatMap flatten tex]

gen_machine :: Bool -> Gen Machine
gen_machine b = do
            nvar  <- choose (0,5)
            types <- L.sort `liftM` vectorOf nvar choose_type
            let vars = map (uncurry $ Var . (:[])) $ zip ['a'..'z'] types
                mch = empty_machine "m0"
                inv_lbl = map (\x -> label $ "inv" ++ show x) [0..]
            ninv <- choose (0,5)
            bs   <- mk_errors b ninv
            invs <- forM bs 
                    (\b -> resize 5 $ expr_type b (symbol_table vars) bool)
            let bk = or (map (\(x,y) -> isJust x && y) $ zip invs bs)
            inv <- if not bk && b then do
                x <- elements [0,5]
                return $ zint x : catMaybes invs
            else return $ catMaybes invs
            return $ (empty_machine "m0")
                { theory = (theory mch) { extends = M.fromList 
                        [ ("sets", set_theory) 
                        , ("functions", function_theory) 
                        , ("arithmetic", arithmetic)
                        , ("basic", basic_theory)] }
                , variables = symbol_table vars
                , props = empty_property_set
                        { inv = M.fromList $ zip inv_lbl inv } }

instance Arbitrary Machine where
    arbitrary = gen_machine False

mk_errors :: Bool -> Int -> Gen [Bool]
mk_errors False n = return $ replicate n False
mk_errors True n = do
    xs <- replicateM (n-1) arbitrary
    permute $ True : xs

expr_type :: Bool -> (M.Map String Var) -> Type -> Gen (Maybe Expr)
expr_type b vars t = sized $ \n ->do
        if n == 0 then 
            choose_var b t
        else do
            oneof 
                [ choose_var b t
                , choose_expr b t
                ]
    where
        t_map = M.fromListWith (++) $ map f $ M.elems vars
        f v@(Var _ t) = (t,[v])
        choose_var b t = do
            t' <- if b then other_type t else return t
            maybe
                (return Nothing)
                (((Just . Word) `liftM`) . elements)
                $ M.lookup t' t_map
        fun_map = M.fromList
            [ (int, 
                [ (from_list zplus, [int,int])])
            , (bool, 
                -- [ (from_list zeq', [int,int]) 
                -- , (from_list zeq, [bool,bool])
                [ (from_list (zand :: Expr -> Expr -> Expr), [bool,bool])
                , (from_list (zor :: Expr -> Expr -> Expr), [bool,bool])
                , (from_list (znot :: Expr -> Expr), [bool])
                , (from_list zle, [int,int])
                , (from_list zelem', [int, set_type int] )])
            ]
        zelem' e0 e1 = FunApp (Fun [int] "elem" [int,set_type int] bool) [e0,e1 :: Expr]
        -- zeq' e0 e1 = FunApp (Fun [] "=" [int,int] bool) [e0,e1 :: Expr]
        choose_expr b t = sized $ \n -> do
            case M.lookup t fun_map of
                Just xs -> do
                    (f,ts) <- elements xs
                    bs     <- mk_errors b $ length ts
                    es     <- forM (zip bs ts) $ \(b,t) -> resize (n-1) $ expr_type b vars t
                    if (all isJust es) then
                        return $ Just $ f $ catMaybes es
                    else 
                        resize (n-1) $ expr_type b vars t
                Nothing -> return Nothing
        --     if t == int then

        --     else if t == bool then

            -- else 

run_spec :: IO Bool
run_spec = $quickCheckAll

-- main = run_spec

show_list :: Show a => [a] -> String
show_list xs = format "[{0}]" $ L.intercalate "\n," $ surround " " " " ys
    where
        ys = map show xs
        surround pre suf xs = map (\x -> pre ++ x ++ suf) xs

subexpression :: Expr -> [(Expr, Type, String)]
subexpression e = f [] e
    where
        f xs e = (e, type_of e, comment e) : visit f xs e
        comment (FunApp (Fun act f argt rt) arg) = format "{0} {1} ({2}) : {3} -> {4}" act f arg argt rt
        comment _ = "<>"

main :: IO ()
main = do
        xs <- liftM concat $ replicateM 10 $ sample' mch_with_type_error
        let (mch,Tex tex) = head 
                $ filter (not . f_prop_type_error . snd) xs
            mch'' = concat $ rights [mch']
            mch'  = (M.elems . machines) `liftM` (all_machines tex)
        writeFile "actual_exp.txt" (unlines $ map (show_list . subexpression) $ concatMap expressions mch'')
        writeFile "expect_exp.txt" (unlines $ map (show_list . subexpression) $ expressions mch)
        writeFile "actual.txt" (show mch')
        writeFile "expect.txt" ("Right " ++ show [mch])
        writeFile "tex.txt" (show $ Tex tex)
        -- print $ zipWith (==) 
        --     (concatMap subexpression $ expressions mch) 
        --     (concatMap subexpression $ concatMap expressions mch')

