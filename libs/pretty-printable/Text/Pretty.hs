{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
module Text.Pretty where

    -- Libraries
import Control.Applicative
import Control.Arrow
import Control.DeepSeq
import Control.Lens hiding (List,cons,uncons)
import Control.Monad.Reader

import Data.Either.Combinators
import Data.Existential
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Hashable as H
import qualified Data.HashMap.Lazy as H
import Data.Maybe
import Data.List as L hiding (uncons,unlines)
import           Data.List.NonEmpty as NE (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.String.Lines

import GHC.Generics
import GHC.Generics.Instances
import GHC.Generics.Lens

import Language.Haskell.TH hiding (Name,report)
import Language.Haskell.TH.Quote

import Prelude hiding (unlines)

newtype Pretty a = Pretty { unPretty :: a }
    deriving (Eq,Ord,Functor,Foldable,Traversable,Hashable,Generic)

class PrettyPrintable a where
    pretty :: a -> String
    default pretty :: (Functor f, Show1 f) => f a -> String
    pretty = show1 . fmap Pretty

instance PrettyPrintable a => Show (Pretty a) where
    show = pretty . unPretty

instance (PrettyPrintable k,Ord k,Hashable k,PrettyPrintable a) 
        => PrettyPrintable (M.Map k a) where
    pretty m = "fromList\n" ++ withMargin "  " "  " (pretty $ M.toList m)

instance (PrettyPrintable k,Ord k,Hashable k,PrettyPrintable a) 
        => PrettyPrintable (H.HashMap k a) where
    pretty m = "fromList\n" ++ withMargin "  " "  " (pretty $ H.toList m)

instance (PrettyPrintable a,PrettyPrintable b) 
        => PrettyPrintable (Either a b) where
    pretty = show . mapBoth Pretty Pretty

instance PrettyPrintable () where
    pretty = show

instance PrettyPrintable (f (g a)) => PrettyPrintable (Compose f g a) where
    pretty = pretty . getCompose

instance PrettyPrintable a => PrettyPrintable [a] where
    pretty = show . L.map Pretty
instance (PrettyPrintable a) => PrettyPrintable (NonEmpty a) where
    pretty xs = "|" ++ pretty (NE.toList xs) ++ "|"
instance (PrettyPrintable a) => PrettyPrintable (Maybe a) where
    pretty = show . fmap Pretty

instance (PrettyPrintable a,PrettyPrintable b)
        => PrettyPrintable (a,b) where
    pretty = show . (Pretty *** Pretty)

instance NFData a => NFData (Pretty a) where

withMargin :: String -> String -> String -> String
withMargin first other = asLines %~ NE.zipWith (++) (first :| repeat other) 

class PrettyRecord a where
    recordFields :: a -> (String,[(String,String)])
    default recordFields 
            :: (Generic a,GenericRecordFields (Rep a))
            => a -> (String,[(String,String)])
    recordFields = genericRecordFields []

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
