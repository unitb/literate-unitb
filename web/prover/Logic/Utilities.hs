module Logic.Utilities where

import           Control.Lens
import qualified Data.Map as M
import           Logic.Expr
import qualified Logic.Theories as Theories
import           Logic.Theories.IntervalTheory (interval_theory)
import           Prelude ((!!))
import           Text.Printf.TH

import           Import

theoryNames :: [String]
theoryNames = render <$> M.keys
    (M.filter (/= interval_theory) Theories.supportedTheories)

varDecl :: Var -> String
varDecl v = render (v^.name) ++ fromMaybe "" (isMember $ type_of v)

withParenth :: Bool -> String -> String
withParenth True  = [printf|(%s)|]
withParenth False = id

isMember :: Type -> Maybe String
isMember t = join (preview (_FromSort.to f) t) <|> ((" \\in " ++) <$> typeToSet False t)
   where
       f (DefSort n _ _ _,ts)
           | n == [tex|\set|] = [printf| \\subseteq %s|] <$> typeToSet False (ts !! 0)
       f _ = Nothing


typeToSet :: Bool -> Type -> Maybe String
typeToSet paren = join . preview (_FromSort.to f)
   where
       f (DefSort n _ _ _,ts)
           | n == [tex|\set|] = withParenth paren . [printf|\\pow.%s|] <$> typeToSet True (ts !! 0)
           | n == [tex|\pfun|] = withParenth paren <$>
                                   liftM2 [printf|%s \\pfun %s|]
                                       (typeToSet True (ts !! 0))
                                       (typeToSet True (ts !! 1))
       f (Sort n _ _,_)
           | otherwise  = Just (render n)
       f (IntSort,[]) = Just [printf|\\mathbb{Z}|]
       f (RealSort,[]) = Just [printf|\\mathbb{R}|]
       f (BoolSort,[]) = Just [printf|\\textbf{Bool}|]
       f _ = Nothing
