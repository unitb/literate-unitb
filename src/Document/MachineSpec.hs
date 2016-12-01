{-# OPTIONS_GHC -fno-warn-orphans #-}
module Document.MachineSpec where
    
    -- Modules
import Document.Document

import Latex.Parser

import Logic.Expr.Parser
import Logic.Operator hiding (Command)

import Logic.Theories.Arithmetic
import Logic.Theories.FunctionTheory
import Logic.Theories.SetTheory

import UnitB.Expr hiding (zelem')
import UnitB.UnitB


    -- Libraries
import Control.Invariant hiding ((===))
import Control.Lens hiding (Context,elements)
import Control.Monad
import Control.Monad.Reader
import Control.Precondition

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import GHC.Generics

import Test.QuickCheck hiding (label, sized, elements)
import Test.QuickCheck.RandomTree
import Test.QuickCheck.Report
import Test.QuickCheck.ZoomEq

import Text.Printf.TH

import qualified Utilities.Graph as G 
import           Utilities.Syntactic

prop_parseOk :: Property
prop_parseOk = forAll correct_machine $ f_prop_parseOk

f_prop_parseOk :: (Pretty RawMachine, Tex) -> Invariant
f_prop_parseOk (Pretty mch,Tex tex) =
        (M.elems . M.map (fmap asExpr) . view' machines) `liftM` (all_machines tex) .== Right [mch]
 
prop_type_error :: Property
prop_type_error = forAll (liftM snd mch_with_type_error) f_prop_type_error

f_prop_type_error :: Tex -> Property
f_prop_type_error (Tex tex) = 
        either (\m -> counterexample (show_err m) $ all is_type_error m) (const $ property False) (all_machines tex) 

prop_expr_parser :: ExprNotation -> Property
prop_expr_parser (ExprNotation ctx n e) = 
        counterexample text $
        counterexample (pretty ctx) $
        e' === parse (withLI text)
    where
        text = showExpr n $ getExpr e
        parse  = fmap getExpr . parse_expr (setting_from_context n ctx & expected_type .~ Nothing)
        e' = Right e
        li = LI "" 0 0
        withLI xs = StringLi (map (\x -> (x,li)) xs) li

data ExprNotation = ExprNotation Context Notation RawExpr
    deriving Generic

instance Show ExprNotation where
     show (ExprNotation _ n e) = showExpr n e

instance Arbitrary ExprNotation where
    arbitrary = sized $ \n -> resize (n `min` 20) $ do
        -- t     <- choose_type
        (vars,e) <- fix (\retry n -> do
            when (n == 0) $ fail "failed to generate ExprNotation"
            vars  <- var_set
            t     <- elements $ bool : (map var_type $ M.elems vars)
            e     <- expr_type False vars t
            case e of
                Just e  -> return (vars,e)
                Nothing -> retry $ n-1
            ) 10
        let ctx = Context 
                    M.empty vars M.empty
                    M.empty M.empty 
        return $ ExprNotation 
                    ctx basic_notation e
    shrink (ExprNotation ctx n e) = mapMaybe (validScope n) . genericShrink $ (ctx,e)
        where
            validScope n (ctx,e)
                | used_var' e `M.isSubmapOf` (ctx^.constants) = Just (ExprNotation ctx n e)
                | otherwise = Nothing

data MachineInput = MachineInput RawMachine [LatexNode]

is_type_error :: Error -> Bool
is_type_error e = 
            "type error:" `L.isInfixOf` msg
        ||  "expected type:" `L.isInfixOf` msg
        ||  "signature:" `L.isInfixOf` msg
    where
        msg = message e

correct_machine :: Gen (Pretty RawMachine, Tex)
correct_machine = machine_input arbitrary

mch_with_type_error :: Gen (Pretty RawMachine, Tex)
mch_with_type_error = machine_input with_type_error

machine_input :: Gen RawMachine -> Gen (Pretty RawMachine, Tex)
machine_input cmd = do
        m   <- cmd
        tex <- latex_of m
        return (Pretty m,Tex tex)

perm :: Int -> Gen [Int]
perm n = permute [0..n-1]

permute :: MonadGen m => [a] -> m [a]
permute xs = liftGen $ permute_aux (length xs) xs

permute_aux :: Int -> [a] -> Gen [a]
permute_aux 0 _  = return []
permute_aux n xs = sized $ \size -> do
        let s_size = round (sqrt $ fromIntegral size :: Double) `max` 2
            buck   = (n `div` s_size) `max` 1
        i  <- choose (0,n-1)
        let ys = drop i xs ++ take i xs
            z = take buck ys
        zs <- permute_aux (n-1) (drop buck ys)
        return $ z ++ zs

showExpr :: (TypeSystem t, IsQuantifier q) => Notation -> AbsExpr Name t q -> String
showExpr notation e = show_e e
    where
        root_op (FunApp f _) = find_op f
        root_op _ = Nothing
        find_op f = view name f `M.lookup` m_ops 
        show_e v@(Word _) = pretty v
        show_e (FunApp f xs) 
            | length xs == 2 = [s|%s %s %s|] 
                                (show_left_sub_e op x)
                                op_name
                                (show_right_sub_e op y)
            | length xs == 1 = [s|%s %s|] 
                                op_name
                                (show_right_sub_e op x)
            | length xs == 0 = error $ [s|show_e: not a binary or unary operator '%s' %s|]
                                    (render $ f^.name)
                                    (L.intercalate ", " $ map pretty xs)
            | otherwise      = show_e (funApp f $ [head xs, funApp f $ tail xs])
            where
                x = xs ! 0
                y = xs ! 1
                op = maybe (Right plus) id $ find_op f
                op_name = maybe unknown (render . view name) $ find_op f
                unknown = [s|<unknown function: %s %s>|] 
                            (render $ f^.name)
                            (show $ map Pretty $ M.keys m_ops)
        show_e (Lit n _) = pretty n
        show_e _ = "<unknown expression>"
        m_ops :: M.Map Name Operator
        m_ops = M.fromList $ zip (map functionName xs) xs
            where
                xs = notation^.new_ops
        show_left_sub_e op e = maybe (show_e e) f $ root_op e
            where
                g op' = (notation^.struct) G.! (op',op)
                f op'
                    | g op' == LeftAssoc = show_e e
                    | otherwise          = [s|(%s)|] $ show_e e
        show_right_sub_e op e = maybe (show_e e) f $ root_op e
            where
                g op' = (notation^.struct) G.! (op,op')
                f op'
                    | g op' == RightAssoc = show_e e
                    | otherwise           = [s|(%s)|] $ show_e e

latex_of :: RawMachine -> Gen LatexDoc
latex_of m = do
        let m_name = BracketNode $ Bracket Curly li 
                           (Doc li [ Text (TextBlock (show $ _name m) li) ] li)
                           li
            show_t t = M.findWithDefault "<unknown>" t type_map
            type_map :: M.Map Type String
            type_map = M.fromList 
                        [ (int, "\\Int")
                        , (bool, "\\Bool")
                        , (set_type int, "\\set[\\Int]")
                        , (fun_type int int, "\\Int \\pfun \\Int")
                        ]
            cmd :: String -> [String] -> [LatexNode]
            cmd n args = Text (Command n li) : concatMap farg args
            farg x = [ BracketNode $ Bracket Curly li (Doc li [ Text (TextBlock x li) ] li) li, blank ]
            var_decl (Var n t) = cmd "\\variable" [(render n ++ " : " ++ show_t t)]
            decls = map var_decl $ M.elems $ m!.variables
            imp_stat :: Name -> [LatexNode]
            imp_stat xs = cmd "\\with" [render xs]
            inv_decl (lbl,xs) = cmd "\\invariant" [pretty lbl, showExpr (all_notation m) xs]
            invs        = map inv_decl $ M.toList $ m!.props.inv
            imports = map imp_stat $ filter (/= makeName "basic") 
                        $ M.keys $ m!.theory.extends
        content <- concat `liftM` permute (decls ++ imports ++ invs)
        return $ Doc li [ EnvNode $ Env li "machine" li 
                          (Doc li ([ m_name, blank ] ++ content) li)
                          li ] li
    where
        li = LI "" 0 0
        blank = Text (Blank "\n" li)

expressions :: IsExpr expr => Machine' expr -> [expr]
expressions m = M.elems $ m!.props.inv

with_type_error :: Gen RawMachine
with_type_error = do
        suchThat (gen_machine True)
             (\m -> not $ L.null $ range m)
    where
        range m = M.elems vars `L.intersect` S.elems fv
            where
                vars  = m!.variables
                fv    = S.unions $ map (used_var.getExpr) $ expressions m

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

data Tex = Tex { unTex :: LatexDoc }

instance Show Tex where
    show (Tex tex) = unlines
            [ "" -- show m
            , flatten' tex]

var_set :: Gen (M.Map Name Var)
var_set = do
    nvar  <- choose (0,5)
    types <- L.sort `liftM` vectorOf nvar choose_type
    let vars = zipWith (Var . makeName . (:[])) ['a'..] types
    return $ symbol_table vars
            
basic_notation :: Notation
basic_notation = th_notation'
                        [ set_theory
                        , function_theory
                        , arithmetic
                        , basic_theory ] 


gen_machine :: Bool -> Gen RawMachine
gen_machine b = fix (\retry n -> do
            when (n == 0) $ fail "failed to produce Machine"
            -- nvar  <- choose (0,5)
            -- types <- L.sort `liftM` vectorOf nvar choose_type
            vars <- var_set
            -- let vars = map (uncurry $ Var . (:[])) $ zip ['a'..'z'] types
            let inv_lbl = map (label . [s|inv%d|]) ([0..] :: [Int])
                            -- map (\x -> label $ "inv" ++ show x) [0..]
            ninv <- choose (0,5)
            bs   <- mk_errors b ninv
            inv <- sequence `liftM` forM bs 
                    (\b -> resize 5 $ expr_type b vars bool)
            case inv of
                Just inv ->
                    return $ newMachine ([tex|m0|]) $ do
                        theory.extends .= symbol_table
                                [ set_theory
                                , function_theory
                                , arithmetic
                                , basic_theory]
                        variables .= vars
                        props .= empty_property_set
                                { _inv = M.fromList $ zip inv_lbl inv } 
                Nothing -> retry $ n-1
            ) 10

instance Arbitrary RawMachine where
    arbitrary = gen_machine False
    -- shrink = content $ \m -> 
    --               [ m & variables .~ vs & abs_vars .~ avs & del_vars .~ dvs 
    --                   & init_witness .~ iwit & inits .~ i 
    --                   -- & event_table .~ et 
    --                   | 
    --         (vs,avs,dvs,(iwit,i)) <- shrink 
    --             (m^.variables
    --             ,m^.abs_vars
    --             ,m^.del_vars
    --             ,(m^.init_witness
    --             ,m^.inits
    --             -- ,m^.event_table
    --             )) ]


mk_errors :: MonadGen m => Bool -> Int -> m [Bool]
mk_errors False n = return $ replicate n False
mk_errors True n = do
    xs <- liftGen $ replicateM (n-1) arbitrary
    permute $ True : xs

expr_type :: Bool -> M.Map Name Var -> Type -> Gen (Maybe RawExpr)
expr_type b vars t = runReaderT (runRec $ expr_type' b t) t_map
    where
        t_map = M.fromListWith (++) $ map f $ M.elems vars
        f v@(Var _ t) = (t,[v])

type EGen = RecT (ReaderT (M.Map Type [Var]) Gen)



expr_type' :: Bool -> Type -> EGen RawExpr
expr_type' b t = do
            choice 
                [ choose_var b t
                , choose_expr b t
                ]
    where

choose_var :: Bool -> Type -> EGen RawExpr
choose_var b t = do
    t' <- if b then liftGen $ other_type t else return t
    t_map <- lift ask
    maybe
        (fail "")
        ((Word `liftM`) . elements)
        $ M.lookup t' t_map

fun_map :: M.Map Type [([RawExpr] -> RawExpr, [Type])]
fun_map = M.fromList
        [ (int, 
            [ (from_list (zplus :: RawExpr -> RawExpr -> RawExpr), [int,int])])
        , (bool, 
            -- [ (from_list zeq', [int,int]) 
            -- , (from_list zeq, [bool,bool])
            [ (from_list (zand :: RawExpr -> RawExpr -> RawExpr), [bool,bool])
            , (from_list (zor :: RawExpr -> RawExpr -> RawExpr), [bool,bool])
            , (from_list (znot :: RawExpr -> RawExpr), [bool])
            , (from_list (zle :: RawExpr -> RawExpr -> RawExpr), [int,int])
            , (from_list zelem', [int, set_type int] )])
        ]

zelem' :: RawExpr -> RawExpr -> RawExpr
zelem' e0 e1 = funApp (mk_fun' [int] "elem" [int,set_type int] bool) [e0,e1 :: RawExpr]
        -- zeq' e0 e1 = funApp (mk_fun [] "=" [int,int] bool) [e0,e1 :: Expr]

choose_expr :: Bool -> Type -> EGen RawExpr
choose_expr b t = do
    case M.lookup t fun_map of
        Just xs -> do
            (f,ts) <- elements xs
            bs     <- mk_errors b $ length ts
            -- es     <- forM (zip bs ts) $ \(b,t) -> resize (n-1) $ expr_type' b t
            es     <- recForM (zip bs ts) $ \(b,t) -> try $ expr_type' b t
            let es' = sequence es
            case es' of
                Just es -> return $ f es
                Nothing -> consume $ expr_type' b t
        Nothing -> fail ""

return []
run_spec :: (PropName -> Property -> IO (a, Result))
         -> IO ([a], Bool)
run_spec = $forAllProperties'

show_list :: Show a => [a] -> String
show_list xs = [s|[%s]|] $ L.intercalate "\n," $ surround " " " " ys
    where
        ys = map show xs
        surround pre suf xs = map (\x -> pre ++ x ++ suf) xs

subexpression :: RawExpr -> [(RawExpr, Type, String)]
subexpression e = f [] e
    where
        f xs e = (e, type_of e, comment e) : visit f xs e
        comment :: RawExpr -> String
        comment (FunApp (Fun act f _ argt rt _) arg) = [s|%s %s (%s) : %s -> %s|] 
                    (pretty act) (render f) 
                    (pretty arg) (pretty argt) 
                    (pretty rt)
        comment _ = "<>"

-- main :: IO ()
-- main = do
--         xs <- liftM concat $ replicateM 100 $ sample' correct_machine
--         let (mch,tex) = head 
--                 $ filter (not . f_prop_parseOk) xs
--             mch'  = (M.elems . view' machines) `liftM` (all_machines $ unTex tex)
        -- print $ tex
        -- print $ mch'
        --     -- txt = showExpr n e
        --     -- txt' = map (\x -> (x,li)) txt
        --     -- mch'' = concat $ rights [mch']
        --     -- mch'  = (M.elems . machines) `liftM` (all_machines tex)
                
        -- writeFile "actual_exp.txt" $ show mch'
        -- writeFile "expect_exp.txt" $ unlines
        --     [ -- show tex
        --     show $ (Right mch :: Either String RawMachine) ]
        -- -- writeFile "actual.txt" (show mch')
        -- -- writeFile "expect.txt" ("Right " ++ show [mch])
        -- -- writeFile "tex.txt" (show $ Tex tex)
        -- -- print $ zipWith (==) 
        -- --     (concatMap subexpression $ expressions mch) 
        -- --     (concatMap subexpression $ concatMap expressions mch')

