{-# LANGUAGE UndecidableInstances
        ,TypeOperators
        ,ScopedTypeVariables
        ,OverloadedStrings #-}
module Logic.Expr.PrettyPrint 
    ( pretty_print', Pretty(..), PrettyPrintable(..) 
    , field
    , prettyRecord, PrettyRecord(..)
    , genericRecordFields )
where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Label
import Logic.Names

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.Invariant
import Control.Lens hiding (List,cons,uncons)
import Control.Monad.Reader

import Data.DList as D (DList)
import qualified Data.DList as D
import Data.DList.Utils as D
import Data.Either.Combinators
import Data.Existential
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Maybe
import Data.Monoid
import Data.List as L hiding (uncons,unlines)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Class as M
import Data.String.Lines

import GHC.Generics
import GHC.Generics.Instances
import GHC.Generics.Lens

import Language.Haskell.TH hiding (Name,report)
import Language.Haskell.TH.Quote

import Prelude hiding (unlines)

import Text.Printf.TH 

import Utilities.Syntactic hiding (line)
import Utilities.Table

pretty_print' :: Tree t => t -> String
pretty_print' t = D.toList $ D.intercalate "\n" 
    $ map toString $ as_list $ fst 
    $ runReader (pretty_print_aux $ as_tree t) ""

newtype Pretty a = Pretty { unPretty :: a }
    deriving (Eq,Ord,Functor,Foldable,Traversable,Hashable)

withMargin :: String -> String -> String -> String
withMargin first other = asLines %~ NE.zipWith (++) (first :| repeat other) 

class PrettyPrintable a where
    pretty :: a -> String
    default pretty :: (Functor f, Show1 f) => f a -> String
    pretty = show1 . fmap Pretty

instance PrettyPrintable a => Show (Pretty a) where
    show = pretty . unPretty

instance PrettyPrintable a => PrettyPrintable (Checked a) where
    pretty = pretty . view content'
instance PrettyPrintable a => PrettyPrintable [a] where
    pretty = show . L.map Pretty
    -- pretty xs = L.intercalate "\n" $ zipWith (\m -> withMargin m "  " . pretty) ("[ " : repeat ", ") xs ++ ["]"]

instance PrettyPrintable StrList where
    pretty = show

instance PrettyPrintable Label where
    pretty = show

instance PrettyPrintable Name where
    pretty = render

instance PrettyPrintable InternalName where
    pretty = render

instance (PrettyPrintable k,Ord k,Hashable k,PrettyPrintable a) 
        => PrettyPrintable (Table k a) where
    pretty m = "fromList\n" ++ withMargin "  " "  " (pretty $ M.toList m)

instance (PrettyPrintable a,PrettyPrintable b) 
        => PrettyPrintable (Either a b) where
    pretty = show . mapBoth Pretty Pretty

instance PrettyPrintable () where
    pretty = show

instance PrettyPrintable (f (g a)) => PrettyPrintable (Compose f g a) where
    pretty = pretty . getCompose

instance PrettyPrintable Error where
    pretty = report

instance (PrettyPrintable a) => PrettyPrintable (NonEmpty a) where
    pretty = [printf||%s||] . pretty . NE.toList
instance (PrettyPrintable a) => PrettyPrintable (Maybe a) where
    pretty = show . fmap Pretty

instance (PrettyPrintable a,PrettyPrintable b)
        => PrettyPrintable (a,b) where
    pretty = show . (Pretty *** Pretty)

instance PrettyPrintable LineInfo where
    pretty (LI _ i j) = [printf|(li:%d:%d)|] i j

class PrettyRecord a where
    recordFields :: a -> (String,[(String,String)])

prettyRecord :: PrettyRecord a => a -> String
prettyRecord r = unlines $ 
        cons :|
        zipWith (++) ("  { " : repeat "  , ")
            [ withMargin f' (margin f') v | (f,v) <- fs, let f' = f ++ " = " ]
        ++ [ "  }", "" ]
    where
        margin f = replicate (length f + 4) ' '
        (cons,fs) = recordFields r

genericRecordFields :: forall a. (Generic a,GenericRecordFields (Rep a))
                    => [Field a]
                    -> a -> (String, [(String,String)])
genericRecordFields excp x = (_1 %~ fromMaybe "") . gRecordFields (L.map unfield excp) . view generic $ x
    where
        unfield :: Field a -> (String, Cell PrettyRecord)
        unfield (Field name y) = (name,runIdentity $ y & traverseCell1 (pure . pure . ($ x))) -- & traverseCell1 %~ (Identity . ($ y)))

data Field a = Field String (Cell1 ((->) a) PrettyRecord)

field :: QuasiQuoter
field = QuasiQuoter 
    { quoteExp  = \f -> [e| Field f $ Cell $(varE $ mkName f) |]
    , quotePat  = undefined
    , quoteType = undefined
    , quoteDec  = undefined
    }

class GenericRecordFields a where
    gRecordFields :: [(String,Cell PrettyRecord)] -> a p -> (Maybe String, [(String,String)])

instance (GenericRecordFields a,GenericRecordFields b) 
        => GenericRecordFields (a :+: b) where
    gRecordFields excp (L1 x) = gRecordFields excp x
    gRecordFields excp (R1 x) = gRecordFields excp x
instance (GenericRecordFields a,GenericRecordFields b) 
        => GenericRecordFields (a :*: b) where
    gRecordFields excp (x :*: y) = (fst rx <|> fst ry, snd rx ++ snd ry)
        where
            rx = gRecordFields excp x
            ry = gRecordFields excp y
instance (Selector s,PrettyPrintable b) => GenericRecordFields (S1 s (K1 a b)) where
    gRecordFields excp x@(M1 (K1 v))
        | Just f <- selName x `L.lookup` excp = (Nothing,snd $ readCell recordFields f)
        | otherwise             = (Nothing,[(selName x,pretty v)])
instance (Constructor c,GenericRecordFields a) => GenericRecordFields (C1 c a) where
    gRecordFields excp m@(M1 x) = gRecordFields excp x & _1 .~ Just (conName m)
instance GenericRecordFields b => GenericRecordFields (D1 a b) where
    gRecordFields excp = gRecordFields excp . unM1

data Line = Line String' String'
-- newtype Line = Line String'

toString :: Line -> String'
toString (Line xs ys) = xs <> ys

line :: Line -> String'
line (Line _ ys) = ys

type String' = DList Char
type M = Reader String'
type X = (List Line,Int)

data List a = Ls (DList a) a

appendL :: List a -> List a -> List a
appendL (Ls xs x) (Ls ys y) = Ls (xs <> D.cons x ys) y

tell' :: String' -> M X
tell' xs = do
    ys <- ask
    return $ (Ls D.empty $ Line ys xs,length xs+1)

appendall :: [(List a, Int)] -> (List a, Int)
appendall ((x0,n):(x1,m):xs) = appendall $ (appendL x0 x1, m+n) : xs
appendall [x] = x
appendall _ = error "appendall: empty list"

cons :: a -> [a] -> List a
cons x xs = Ls (D.fromList $ init ys) (last ys)
    where
        ys = x:xs

uncons :: List a -> (a -> [a] -> b) -> b
uncons ls f = f (head zs) (tail zs)
    where
        zs = as_list ls

as_list :: List a -> [a]
as_list (Ls xs x) = D.apply xs [x]

pretty_print_aux :: StrList -> M X
pretty_print_aux (Str xs) = tell' $ D.fromList xs
pretty_print_aux (List []) = tell' "()"
pretty_print_aux (List ys@(x:xs)) = 
        case x of
            Str y'    -> do
                zz <- mapM pretty_print_aux xs
                let one_line' = D.concatMap (" " <>) $ L.concatMap (L.map line . as_list . fst) zz
                    k = sum $ map snd zz
                    y = D.fromList y'
                if k <= 50
                then tell' $ "(" <> y <> one_line' <> ")"
                else do
                    zs <- prefix_first ("(" <> y <> " ") $
                        mapM pretty_print_aux xs
                    return $ add_to_last ")" $ appendall zs
            List _ -> do
                zs <- prefix_first "( " $
                    mapM pretty_print_aux ys
                return $ add_to_last " )" $ appendall zs
    where
        prefix_first :: String' -> M [X] -> M [X]
        prefix_first xs cmd = do
            let k = length xs
            ys <- indent k cmd 
            case ys of
                [] -> (:[]) `liftM` tell' xs
                (ls, n):ys -> 
                    uncons ls $ \(Line m y) zs -> do
                        let newLine = Line (m & asList %~ take (length m - k)) (xs <> y)
                        return $ (cons newLine zs, n+k):ys
        indent n cmd = do
            local (margin n <>) cmd
        margin n = D.fromList $ L.replicate n ' '
        add_to_last suff (Ls xs (Line x y),k) = (Ls xs (Line x $ y<>suff),k)
  
-- pretty_print :: StrList -> [String]
-- pretty_print (Str xs) = [xs]
-- pretty_print (List []) = ["()"]
-- pretty_print (List ys@(x:xs)) = 
--         case x of
--             Str y    -> 
--                 if length one_line <= 50
--                 then ["(" ++ y ++ " " ++ one_line ++ ")"]
--                 else
--                     zipWith (++)
--                         (("(" ++ y ++ " "):repeat (margin (length y + 2)))
--                         (add_to_last ")" zs)
--             List _ -> zipWith (++)
--                 ("( ":repeat (margin 2))
--                 (add_to_last " )" zs')
--     where
--         margin n = replicate n ' '
--         add_to_last suff xs = 
--             case reverse xs of
--                 y:ys -> reverse ( (y++suff):ys )
--                 []        -> [suff]
--         zs = concatMap pretty_print xs
--         zs' = concatMap pretty_print ys
--         one_line = intercalate " " zs
