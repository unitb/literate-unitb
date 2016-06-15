module Latex.Test where

    -- Modules
import Latex.Parser 
import Latex.Monad
import Latex.Scanner

    -- Libraries
import Control.Arrow ((&&&))
import Control.Applicative
import Control.Lens
import Control.Monad.State

import Data.Char
import Data.Either.Combinators
import qualified Data.List as L
import qualified Data.Map as M 
import qualified Data.Maybe as MM

import GHC.Generics.Instances

import Test.UnitTest
import Test.QuickCheck as QC hiding (sized)
import Test.QuickCheck.RandomTree hiding (size,subtrees)
import Test.QuickCheck.Regression
import Test.QuickCheck.Report

import Text.Printf.TH
import Text.Show.With

import Utilities.Syntactic

path2 :: FilePath
path2 = "Tests/sample.tex"

result2 :: String
result2 = 
     "Right (fromList [(\"align\",[]),(\"calculation\",[Env{calculation} (59),Env{calculation} (29)]),(\"equation\",[]),(\"invariant\",[]),(\"lemma\",[]),(\"machine\",[]),(\"theorem\",[])])"
    

path3 = "Tests/sorted_sequences_err.tex"
path3 :: FilePath

result3 :: String
result3 = concat
    [ "Left [Error \"unexpected: }; expected: node; expected: end keyword (equation)\" (LI \"\" 29 13)]"
    ]

path4 = "Tests/sorted_sequences.tex"
path4 :: FilePath

path5 = "Tests/integers.tex"
path5 :: FilePath

sections :: [String]
sections = [
    "calculation",
    "theorem",
    "equation",
    "align",
    "lemma",
    "invariant",
    "machine"]

extract_structure :: String -> Either [Error] (M.Map String [LatexNode])
extract_structure ct = do
    xs <- latex_structure "" ct
    return (find_env sections xs)

find_env :: [String] -> LatexDoc -> M.Map String [LatexNode]
find_env kw xs = M.map reverse $ L.foldl' f (M.fromList $ zip kw $ repeat []) $ contents' xs
    where
        f m (t@(EnvNode (Env _ name _ _ _)))
            | name `elem` kw = M.insertWith (++) name [t] m
            | otherwise        = fold_doc f m t
        f m t                  = fold_doc f m t

main :: FilePath -> IO String
main path = do
        let f (EnvNode (Env _ n _ doc _))   = ShowString $ [printf|Env{%s} (%d)|] n (length $ contents' doc)
            f (BracketNode (Bracket _ _ doc _)) = ShowString $ [printf|Bracket (%d)|] (length $ contents' doc)
            f (Text _)            = ShowString "Text {..}"
        ct <- readFile path
        return $ show $ M.map (map f) <$> extract_structure ct

tests :: FilePath -> IO String
tests path = do
        ct <- readFile path
        let x = (do
                tree <- latex_structure path ct
                return (flatten' tree))
        return (case x of
            Right xs -> xs
            Left msgs -> error $ L.unlines $ map report msgs)

instance Arbitrary LatexToken where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance Arbitrary LatexDoc where
    arbitrary = sized $ \sz -> makeLatex "foo.txt" <$> aux (ceiling $ fromIntegral sz ** (1.5 :: Float) + 1)
        where
            char = arbitrary `suchThat` \c -> isPrint c && c `notElem` "%{}[]\\"
            cmd  = char `suchThat` (not.isSpace)
            aux :: Int -> Gen (LatexGen ())
            aux sz = do
                oneof $ concat
                    [ [ do
                        name <- listOf1 cmd
                        n    <- choose (0,sz-2)
                        bins <- subtree_size (n+1) sz
                        ts   <- mapM aux (tail bins)
                        begin name ts <$> aux (head bins)
                      , brackets <$> aux (sz - 1) ]
                    | sz > 1 ] ++
                    [ text <$> listOf char ]
    shrink = map (makeLatex "foo.txt" . texMonad) . sort . subtrees
        where
            sort = map (($ ()) . snd) . L.sortOn fst . map (sz &&& id)
            sz x = size (x ())

newtype Tokens = TokenStream [(LatexToken,LineInfo)]
    deriving (Generic)

instance Show Tokens where
    show (TokenStream xs) = show xs

instance Arbitrary BracketType where
    arbitrary = QC.elements [Curly,Square]

instance Arbitrary Tokens where
    arbitrary = do
        let true = const True
            li   = LI "foo.txt" 1 1
            char = arbitrary `suchThat` (`notElem` "\\[]{}%") `suchThat` (not . isSpace)
        xs <- listOf $ return $ do
            (p,li) <- get
            (x,s') <- lift $ oneof 
                [ do 
                    t <- Open <$> arbitrary <*> pure li
                    return ((t,li),(true,end (t,li)))
                , do 
                    t <- Close <$> arbitrary <*> pure li
                    return ((t,li),(true,end (t,li)))
                , do 
                    t <- TextBlock <$> listOf1 char <*> pure li
                    return ((t,li),(isn't _TextBlock,end (t,li)))
                , do 
                    t <- Command <$> (('\\':) <$> ((:) <$> (char `suchThat` isAlpha)
                                                       <*> listOf (char `suchThat` isAlphaNum))) 
                                 <*> pure li
                    return ((t,li),(isn't _TextBlock,end (t,li)))
                , do 
                    t <- Blank <$> listOf1 (arbitrary `suchThat` isSpace) 
                               <*> pure li
                    return ((t,li),(isn't _Blank,end (t,li)))
                ] `suchThat` (p.fst.fst)
            put s'
            return x
        ts <- evalStateT (sequence xs) (true,li)
        return $ TokenStream ts
    shrink = genericShrink

instance Arbitrary MutatedTokens where
    arbitrary = do
        (important,ts) <- suchThat (do
            ts <- tokens <$> arbitrary
            let p :: Traversal' a b -> (z,(a,w)) -> Maybe (z,(a,w))
                p pr x = x <$ (x^?_2._1.pr)
                begin :: Traversal' LatexToken ()
                begin = _Command . _1 . only "\\begin" 
                end :: Traversal' LatexToken ()
                end = _Command . _1 . only "\\end"
                important = MM.mapMaybe (\x -> p _Open x <|> p _Close x <|> p end x <|> p begin x) $ zip [0..] ts
            return (important,ts)) (not . null . fst)
        i <- QC.elements $ map fst important
        return $ MutatedTokens $ take i ts ++ drop (i+1) ts

newtype MutatedTokens = MutatedTokens [(LatexToken,LineInfo)]
    deriving (Show)

prop_flatten_parse_inv :: LatexDoc -> Property
prop_flatten_parse_inv t = Right t === latex_structure "foo.txt" (flatten t)

prop_flatten_parse_inv_regression :: Property
prop_flatten_parse_inv_regression = regression prop_flatten_parse_inv $
    [ Doc (LI "foo.txt" 1 1) [Text (TextBlock "\247" (LI "foo.txt" 1 1))] (LI "foo.txt" 1 2) 
    , Doc (LI "foo.txt" 1 1) [Text (TextBlock "=s" (LI "foo.txt" 1 1))] (LI "foo.txt" 1 3) 
    , Doc (LI "foo.txt" 1 1) [EnvNode $ Env (LI "foo.txt" 1 1) "\"" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 10) [] (LI "foo.txt" 1 10)) (LI "foo.txt" 1 15)] (LI "foo.txt" 1 17)
    , Doc (LI "foo.txt" 1 1) [EnvNode $ Env (LI "foo.txt" 1 1) "\202" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 10) [Text (TextBlock "H" (LI "foo.txt" 1 10))] (LI "foo.txt" 1 11)) (LI "foo.txt" 1 16)] (LI "foo.txt" 1 18)
    ]

prop_parse_error :: MutatedTokens -> Bool
prop_parse_error (MutatedTokens ts) = isLeft $ latex_structure "foo.txt" (flatten ts)

prop_makeLatex_latexMonad_inverse :: LatexDoc -> Property
prop_makeLatex_latexMonad_inverse t = t === makeLatex "foo.txt" (texMonad t)

prop_flatten_scan_inv :: LatexDoc -> Property
prop_flatten_scan_inv t = Right (tokens t) === scan_latex "foo.txt" (flatten t)

prop_flatten_scan_inv_regression :: Property
prop_flatten_scan_inv_regression = regression prop_flatten_scan_inv cases
    where
        cases = 
            [ Doc (LI "foo.txt" 1 1) [EnvNode $ Env (LI "foo.txt" 1 1) "\232y\171" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 12) [Text (TextBlock "\181" (LI "foo.txt" 1 12))] (LI "foo.txt" 1 13)) (LI "foo.txt" 1 18)] (LI "foo.txt" 1 22)
            ]

prop_uncomment_inv :: String -> Property
prop_uncomment_inv xs' = xs === uncomment xs
    where
        xs = filter (/= '%') xs'

prop_uncomment_inv_regression :: Property
prop_uncomment_inv_regression = regression prop_uncomment_inv cases
    where
        cases =
            [ "\r" ]

prop_line_number_inv :: String -> Property
prop_line_number_inv xs = xs === map fst (line_number "" xs)

prop_line_number_inv_regression :: Property
prop_line_number_inv_regression = regression prop_line_number_inv cases
    where
        cases =
            [ "\n" ]

prop_flatten_scan_inv' :: Tokens -> Property
prop_flatten_scan_inv' (TokenStream toks) = Right toks === scan_latex "foo.txt" (concatMap lexeme $ map fst toks)

prop_flatten_scan_inv'_regression :: Property
prop_flatten_scan_inv'_regression = regression prop_flatten_scan_inv' cases
    where
        cases = 
            [ TokenStream [(Command "\\v" (LI "foo.txt" 1 1),(LI "foo.txt" 1 1)),(Command "\\Gr8z\200" (LI "foo.txt" 1 3),(LI "foo.txt" 1 3)),(Blank "\r\r" (LI "foo.txt" 1 9),(LI "foo.txt" 1 9))]
            ]

prop_non_empty_parse_error :: MutatedTokens -> Property
prop_non_empty_parse_error (MutatedTokens toks) = isLeft xs ==> all (not . null . message) (fromLeft' xs)
    where 
        xs = latex_structure "foo.txt" (flatten toks)

prop_non_empty_scan_error :: String -> Bool
prop_non_empty_scan_error str = isRight $ scan_latex "foo.txt" str

--prop_counter_example0 :: Bool
--prop_counter_example0 = Right counter0 === counter0'

--prop_counter_example1 :: Bool
--prop_counter_example1 = Right counter1 === counter1'

counter0 :: LatexDoc
counter0 = Doc (LI "foo.txt" 1 1) [EnvNode $ Env (LI "foo.txt" 1 1) "\232y\171" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 12) [Text (TextBlock "\181" (LI "foo.txt" 1 12))] (LI "foo.txt" 1 13)) (LI "foo.txt" 1 18)] (LI "foo.txt" 1 22)
    --Doc (LI "foo.txt" 1 1) [Env (LI "foo.txt" 1 1) "r" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 10) [Text (TextBlock "K" (LI "foo.txt" 1 10))] (LI "foo.txt" 1 11)) (LI "foo.txt" 1 11)] (LI "foo.txt" 1 18)

counter0' :: [(LatexToken,LineInfo)]
counter0' = fromRight' $ scan_latex "foo.txt" (flatten counter0)

counter1 :: [(LatexToken,LineInfo)]
counter1 = [(Close Curly (LI "foo.txt" 1 1),(LI "foo.txt" 1 1)),(TextBlock "Bhb~\US\249c&?" (LI "foo.txt" 1 2),(LI "foo.txt" 1 2)),(Blank "\f\v \v \160\n\f\v" (LI "foo.txt" 1 11),(LI "foo.txt" 1 11)),(TextBlock "8N-P\183JM\249\ESC\138" (LI "foo.txt" 2 3),(LI "foo.txt" 2 3)),(Close Square (LI "foo.txt" 2 13),(LI "foo.txt" 2 13)),(Close Square (LI "foo.txt" 2 14),(LI "foo.txt" 2 14)),(Open Square (LI "foo.txt" 2 15),(LI "foo.txt" 2 15)),(TextBlock "!mKJh\US\233" (LI "foo.txt" 2 16),(LI "foo.txt" 2 16)),(Blank "\n \f\f\n" (LI "foo.txt" 2 23),(LI "foo.txt" 2 23))]
    -- "\\begin{5}{{~B}}\\end{5}"
    --Doc (LI "foo.txt" 1 1) [Env (LI "foo.txt" 1 1) "5" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 10) [Bracket Curly (LI "foo.txt" 1 10) (Doc (LI "foo.txt" 1 11) [Bracket Curly (LI "foo.txt" 1 11) (Doc (LI "foo.txt" 1 12) [Text (TextBlock "~B" (LI "foo.txt" 1 12))] (LI "foo.txt" 1 14)) (LI "foo.txt" 1 14)] (LI "foo.txt" 1 15)) (LI "foo.txt" 1 15)] (LI "foo.txt" 1 16)) (LI "foo.txt" 1 21)] (LI "foo.txt" 1 23)

counter1' :: [(LatexToken,LineInfo)]
counter1' = fromRight' $ scan_latex "foo.txt" (concatMap lexeme $ map fst counter1)

--counter2 :: LatexDoc
--counter2 = Doc (LI "foo.txt" 1 1) [Env (LI "foo.txt" 1 1) "l\241V\203" (LI "foo.txt" 1 8) (Doc (LI "foo.txt" 1 13) [Bracket Curly (LI "foo.txt" 1 13) (Doc (LI "foo.txt" 1 14) [Env (LI "foo.txt" 1 14) "\177+" (LI "foo.txt" 1 21) (Doc (LI "foo.txt" 1 24) [] (LI "foo.txt" 1 24)) (LI "foo.txt" 1 24)] (LI "foo.txt" 1 32)) (LI "foo.txt" 1 32),Bracket Curly (LI "foo.txt" 1 33) (Doc (LI "foo.txt" 1 34) [Env (LI "foo.txt" 1 34) "? /s" (LI "foo.txt" 1 41) (Doc (LI "foo.txt" 1 46) [Text (TextBlock "\212Y" (LI "foo.txt" 1 46))] (LI "foo.txt" 1 48)) (LI "foo.txt" 1 48)] (LI "foo.txt" 1 58)) (LI "foo.txt" 1 58),Bracket Curly (LI "foo.txt" 1 59) (Doc (LI "foo.txt" 1 60) [Text (TextBlock "Z\190:" (LI "foo.txt" 1 60))] (LI "foo.txt" 1 63)) (LI "foo.txt" 1 63),Bracket Curly (LI "foo.txt" 1 64) (Doc (LI "foo.txt" 1 65) [Text (TextBlock "i\230*" (LI "foo.txt" 1 65))] (LI "foo.txt" 1 68)) (LI "foo.txt" 1 68),Bracket Curly (LI "foo.txt" 1 69) (Doc (LI "foo.txt" 1 70) [Text (TextBlock "k4" (LI "foo.txt" 1 70))] (LI "foo.txt" 1 72)) (LI "foo.txt" 1 72),Bracket Curly (LI "foo.txt" 1 73) (Doc (LI "foo.txt" 1 74) [Bracket Curly (LI "foo.txt" 1 74) (Doc (LI "foo.txt" 1 75) [Env (LI "foo.txt" 1 75) "j" (LI "foo.txt" 1 82) (Doc (LI "foo.txt" 1 84) [Bracket Curly (LI "foo.txt" 1 84) (Doc (LI "foo.txt" 1 85) [Text (TextBlock "6\240n" (LI "foo.txt" 1 85))] (LI "foo.txt" 1 88)) (LI "foo.txt" 1 88)] (LI "foo.txt" 1 89)) (LI "foo.txt" 1 89)] (LI "foo.txt" 1 96)) (LI "foo.txt" 1 96)] (LI "foo.txt" 1 97)) (LI "foo.txt" 1 97),Bracket Curly (LI "foo.txt" 1 98) (Doc (LI "foo.txt" 1 99) [] (LI "foo.txt" 1 99)) (LI "foo.txt" 1 99),Bracket Curly (LI "foo.txt" 1 100) (Doc (LI "foo.txt" 1 101) [] (LI "foo.txt" 1 101)) (LI "foo.txt" 1 101),Bracket Curly (LI "foo.txt" 1 102) (Doc (LI "foo.txt" 1 103) [Text (TextBlock ")h" (LI "foo.txt" 1 103))] (LI "foo.txt" 1 105)) (LI "foo.txt" 1 105)] (LI "foo.txt" 1 106)) (LI "foo.txt" 1 106)] (LI "foo.txt" 1 116)
----counter2 = "{%\220Y+B}{kk\196}{eX*pi}{\\begin{92>xc}bob\\end{92>xc}}{\\begin{Nr}\229\&4\\end{Nr}}{+#\231\164}}\\end{Q}}}"

--counter2' :: Either [Error] [(LatexToken, LineInfo)]
--counter2' = Right $ tokens counter2

--counter2'' :: Either [Error] [(LatexToken, LineInfo)]
--counter2'' = scan_latex "foo.txt" (flatten counter2)


return []

properties :: (PropName -> Property -> IO (a, Result))
           -> IO ([a], Bool)
properties = $forAllProperties'

cases :: TestCase
cases = test_cases "latex parser" [
    (QuickCheckProps "quickcheck" properties),
    (aCase "sample.tex" (main path2) result2),
    (aCase "sorted seq err.tex" (main path3) result3),
    (CalcCase "reconstitute sample.tex" 
        (tests path2) 
        (uncomment <$> readFile path2)),
    (CalcCase "reconstitute integers.tex" 
        (tests path5) 
        (uncomment <$> readFile path5)),
    (CalcCase "reconstitute sorted seq.tex" 
        (tests path4) 
        (uncomment <$> readFile path4)) ]

test_case :: TestCase
test_case = cases

