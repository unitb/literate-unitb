{-# LANGUAGE TypeFamilies #-}
module Logic.Names.Internals 
    ( Name(Name), InternalName(InternalName)
    , isZ3Name, isZ3Name'
    , IsBaseName(..)
    , Translatable(..)
    , makeName
    , make, make'
    , isName, isName'
    , assert
    , fromString'
    , fresh
    , reserved
    , dropSuffix 
    , addSuffix
    , addBackslash
    , setSuffix
    , Encoding(Z3Encoding)
    , check_props )
where

    -- Libraries
import Control.DeepSeq
import Control.Lens
import Control.Monad.State

import Data.Char
import Data.Data
import Data.Either.Combinators
import Data.List as L
import qualified Data.List.Ordered as Ord
import Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Serialize
import Data.Semigroup hiding (option)
import Data.String.Utils
import Data.Tuple
import Data.Word

import Language.Haskell.TH.Syntax (Lift(..))

import Text.Printf

import Utilities.Instances
import Utilities.Invariant hiding ((===))
import Utilities.Language  as Lang
import Utilities.Packaged
import Utilities.Partial

import Test.QuickCheck as QC

    -- ^ Names can be specified in Z3 or in LaTeX encoding
    -- ^ They can then be rendered in either Z3 or LaTeX
    -- ^ by using `substToZ3` and `substToLatex` to translate them
data Name = Name 
        { _backslash :: Bool 
        , _base :: NullTerminatedNEString 
        , _primes :: Word8 
        , _suffix :: NullTerminatedString
        , _encoding :: Encoding }
    deriving (Data,Generic,Show,Eq,Ord)

name :: Bool -> NullTerminatedNEString
             -> Word8
             -> NullTerminatedString
             -> Encoding
             -> Name
name = Name

data Encoding = Z3Encoding | LatexEncoding
    deriving (Eq,Ord,Data,Generic,Show)

makeLenses ''Name

data InternalName = InternalName NullTerminatedString Name NullTerminatedString
    deriving (Eq,Ord,Data,Generic,Show)

class (Show a,Ord a,Data a) => IsBaseName a where
    render :: a -> String
    --asString :: Assert -> Iso' a String
    asInternal' :: a -> InternalName
    asName'  :: a -> Name
    fromString'' :: (?loc :: CallStack) => String -> a
    addPrime :: a -> a
    generateNames :: a -> [a]
    language :: Proxy a -> Language a
    texName :: (?loc :: CallStack) 
            => String -> a
    z3Name :: (?loc :: CallStack) 
           => String -> a

--instance Show Name where
--    show = printf "[%s]" . render

--instance Show InternalName where
--    show x = printf "{%s}" $ render x

toZ3Encoding :: Name -> Name
toZ3Encoding n = case n^.encoding of
    LatexEncoding -> n & base._Wrapped' %~ replaceAll' assert substToZ3
                       & suffix._Wrapped' %~ replaceAll substToZ3
                       & encoding .~ Z3Encoding
    Z3Encoding -> n

toLatexEncoding :: Name -> Name
toLatexEncoding n = case n^.encoding of
    Z3Encoding -> n & base._Wrapped' %~ replaceAll' assert substToLatex
                    & suffix._Wrapped' %~ replaceAll substToLatex
                    & encoding .~ LatexEncoding
    LatexEncoding -> n

instance IsBaseName Name where
    render n = concat [slash,toList base,replicate (fromIntegral p) '\'',suffix]
        where
            (Name b (NullTerm base) p (NullTerm suff) _) = toLatexEncoding n
            slash  | b          = "\\"
                   | otherwise  = ""
            suffix | L.null suff = ""
                   | otherwise   = printf "_{%s}" suff
    --asString arse = iso render $ makeName arse
    asInternal' n = InternalName (NullTerm "") n (NullTerm "")
    asName' = id
    fromString'' xs = makeName (withCallStack $ withMessage "makeName" (show xs) assert) xs
    --addSuffix (Name n0) n1 = Name $ n0 <> ('@' :| n1)
    --dropSuffix (Name (n:|ns)) = Name $ n :| L.takeWhile ('@' /=) ns
    addPrime = primes %~ (+1)
    generateNames n = n : [ n & base._Wrapped' %~ (<+ show i) | i <- [0..] ]
    language Proxy = latexName
    z3Name = fromJust' . isZ3Name'
    texName = fromString''

fresh :: IsBaseName n => n -> M.Map n b -> n
fresh name xs = L.head $ ys `Ord.minus` M.keys xs
    where
        ys = generateNames name

make :: (?loc :: CallStack,IsBaseName n0,IsBaseName n1)
     => (n0 -> n1 -> a)
     -> String -> String -> a
make f inm = make' (make' f inm)
    --f (fromString'' inm) (makeName (withCallStack assert) nm)

make' :: (?loc :: CallStack,IsBaseName n)
      => (n -> a)
      -> String -> a
make' f = f . fromString''

--instance IsString Name where
--    fromString = fromString''

(<+) :: NonEmpty a -> [a] -> NonEmpty a
(<+) (x :| xs) ys = x :| (xs ++ ys)

--numbers :: Int -> [InternalName]
--numbers n = L.map (fromString''.show) [1..n]

instance IsBaseName InternalName where
    render (InternalName (NullTerm pre) x (NullTerm suf)) = prefix ++ z3Render x ++ suf
        where
            prefix | null pre  = ""
                   | otherwise = printf "@@%s@@_" pre
            --suffix | null suf  = ""
            --       | otherwise = "@" ++ suf
    --asString arse = iso render $ fromString' arse
    asInternal' = id
    asName' (InternalName _ n _) = n
    fromString'' str = fromString' (withMessage "InternalName.fromString''" (show str) assert) str
    --fresh (InternalName name) xs = L.head $ ys `Ord.minus` M.keys xs
    --    where
    --        ys = L.map InternalName $ name : L.map f [0..]
    --        f x = name <: show x
    addPrime = internal %~ addPrime
    generateNames (InternalName pre n suf) = 
            InternalName pre <$> generateNames n <*> pure suf
    language Proxy = asInternal' <$> z3Name'
    z3Name str = asInternal' $ (z3Name str :: Name)
    texName str = asInternal' $ (texName str :: Name)


z3Render :: Name -> String
z3Render n = concat $ [slash,NE.toList xs] ++ replicate (fromIntegral ps) "@prime" ++ [suf']
    where
        slash | sl        = "sl@"
              | otherwise = ""
        (Name sl (NullTerm xs) ps (NullTerm suf) _) 
                = toZ3Encoding n
        suf' | null suf  = ""
             | otherwise = "@" ++ suf

setSuffix :: Assert -> String -> Name -> Name
setSuffix _ suff = suffix .~ NullTerm suff

fromString' :: Assert -> String -> InternalName
fromString' arse nm = InternalName (NullTerm "") (fromJust'' arse $ isZ3Name' n) (NullTerm suf)
    where
        (n,suf) = L.span ('@' /=) nm


isZ3Name' :: String -> Maybe Name
isZ3Name' x = either (const Nothing) Just $ isZ3Name x
    --parse z3Name' "" x

isZ3Name :: String -> Either [String] Name
isZ3Name str = mapLeft (\x -> [err,show x]) $ parse' z3Name' "" str
    where
        err = printf "invalid name: '%s'" str

isName :: String -> Either [String] Name
isName str = mapBoth (\x -> [err,show x]) toZ3Encoding $ parse' latexName "" str
    where
        err = printf "invalid name: '%s'" str

isName' :: String -> Maybe Name
isName' = either (const Nothing) Just . isName

makeName :: Assert -> String -> Name
makeName arse = fromJust'' arse . isName'

addBackslash :: Name -> Name
addBackslash = backslash .~ True

addSuffix :: String -> InternalName -> InternalName
addSuffix n1 (InternalName pre n0 suf) = InternalName pre n0 $ suf & _Wrapped' %~ (++ n1)

dropSuffix :: InternalName -> InternalName
dropSuffix (InternalName pre ns _) = InternalName pre ns (NullTerm "")




reserved :: String -> Int -> InternalName
reserved pre n = InternalName (NullTerm pre) (makeName assert $ show n) (NullTerm "")

internal :: Lens' InternalName Name
internal f (InternalName pre n suf) = (\n' -> InternalName pre n' suf) <$> f n
 
z3Name' :: Language Name
z3Name' = ($ Z3Encoding) <$> (symb <|> name)
    where
        name = 
            Name <$> option False (try (string "sl@" >> pure True)) 
                 <*> (NullTerm <$> many1' (alphaNum <|> char '-'))
                 <*> (fromIntegral.L.length 
                        <$> many (string "@prime"))
                 <*> pure (NullTerm "")
        symb = Name False . sconcat <$> many1' symbol <*> pure 0 <*> pure (NullTerm "")

latexName :: Language Name
latexName = ($ LatexEncoding) <$> (symb <|> name)
    where
        name = 
            Name <$> option False (string "\\" >> pure True) 
                 <*> (NullTerm <$> many1' (alphaNum <|> char '_'))
                 <*> (fromIntegral.L.length 
                        <$> many (string "\'"))
                 <*> pure (NullTerm "")
        symb = Name False <$> symbol' <*> pure 0 <*> pure (NullTerm "")
        symbol' = symbol <|> texSymbol

texSymbol :: Language NullTerminatedNEString
texSymbol = (NullTerm.(:| [])) <$> oneOf [';','.']

symbol :: Language NullTerminatedNEString
symbol = (NullTerm.(:| []) <$> (oneOf ['-','*','/'] <|> satisfy isSymbol)) <?> "symbol"

substToZ3 :: [(String,String)]
substToZ3 = [("\\","sl@")
            --,("_","@sub@")
            ,("'","@prime")
            ]

substToLatex :: [(String,String)]
substToLatex = L.map swap substToZ3

replaceAll' :: Assert -> [(String,String)] -> NonEmpty Char -> NonEmpty Char
replaceAll' arse sub = nonEmpty' arse . replaceAll sub . toList

replaceAll :: [(String,String)] -> String -> String
replaceAll = execState . mapM_ (modify . uncurry replace)

prop_subst_idempotent :: String -> Property
prop_subst_idempotent xs = replaceAll substToZ3 (replaceAll substToZ3 xs) === replaceAll substToZ3 xs

prop_rev_substToZ3_idempotent :: String -> Property
prop_rev_substToZ3_idempotent xs = replaceAll substToLatex (replaceAll substToLatex xs) === replaceAll substToLatex xs

prop_subst_order_independent :: String -> Property
prop_subst_order_independent xs = forAll (shuffle substToZ3) $ \s -> replaceAll s xs === replaceAll substToZ3 xs

prop_rev_subst_order_independent :: String -> Property
prop_rev_subst_order_independent xs = forAll (shuffle substToLatex) $ \s -> replaceAll s xs === replaceAll substToLatex xs

prop_subst_left_inv :: Name -> Property
prop_subst_left_inv xs = 
        replaceAll substToLatex (replaceAll substToZ3 $ render xs) === render xs

prop_subst_right_inv :: InternalName -> Property
prop_subst_right_inv xs = 
        replaceAll substToZ3 (replaceAll substToLatex $ render xs) === render xs

prop_subst_preserves_non_emptiness :: NonEmptyList Char -> Property
prop_subst_preserves_non_emptiness (NonEmpty xs) = replaceAll substToZ3 xs =/= []

prop_substToLatex_preserves_non_emptiness :: NonEmptyList Char -> Property
prop_substToLatex_preserves_non_emptiness (NonEmpty xs) = replaceAll substToLatex xs =/= []

-- prop: eq render == eq names

--nonEmptyOf :: Gen a -> Gen (NonEmpty a)
--nonEmptyOf gen = (:|) <$> gen <*> listOf gen

infix 4 =/=
(=/=) :: (Eq a, Show a) => a -> a -> Property
x =/= y = counterexample (show x ++ " == " ++ show y) (x /= y)

instance Arbitrary Name where
    arbitrary = do
        oneof 
            [ word latexName
            , word z3Name' ]

instance Arbitrary InternalName where
    arbitrary = do
        asInternal' <$> (arbitrary :: Gen Name)

instance Lift Name where
    lift (Name a b c d e) = [e| name a b c d e |]
instance Lift Encoding where
    lift = genericLift
instance Lift InternalName where
    lift = genericLift

instance NFData Encoding where
instance NFData Name where
instance NFData InternalName where
instance Serialize Encoding where
instance Serialize Name where
instance Serialize InternalName where
instance Serialize a => Serialize (NonEmpty a) where

class Translatable a b | a -> b where
    translate :: a -> b

return []

check_props :: IO Bool
check_props = $quickCheckAll
