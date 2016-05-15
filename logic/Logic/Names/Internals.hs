{-# LANGUAGE TypeFamilies,CPP #-}
module Logic.Names.Internals 
    ( module Logic.Names.Internals
    , NonEmpty((:|))
    )
where

    -- Libraries
import Control.DeepSeq
import Control.Lens
import Control.Monad
import Control.Monad.State
import Control.Precondition

import Data.Char
import Data.Data
import Data.Either.Combinators
import Data.List as L
import Data.List.Lens as L
import qualified Data.List.Ordered as Ord
import Data.List.NonEmpty as NE
import qualified Data.Map.Class as M
import Data.Serialize
import Data.Semigroup hiding (option)
import Data.Tuple
import Data.Word

import GHC.Generics.Instances

import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (Name,lift)
import qualified Language.Haskell.TH.Syntax as TH 

import Test.QuickCheck as QC
import Test.QuickCheck.Regression as QC
import Test.QuickCheck.Report as QC

import Text.Pretty
import Text.Printf.TH

import Utilities.Language  as Lang
import Utilities.Table

type NEString = NonEmpty Char

#ifdef __LAZY_NAME__

    -- ^ Names can be specified in Z3 or in LaTeX encoding
    -- ^ They can then be rendered in either Z3 or LaTeX
    -- ^ by using `substToZ3` and `substToLatex` to translate them
data Name = Name 
        { _backslash :: Bool 
        , _base :: NEString 
        , _primes :: Word8 
        , _suffix :: String
        } deriving (Data,Generic,Eq,Ord,Show)

data InternalName = InternalName String Name String
    deriving (Eq,Ord,Data,Generic,Show)

#else

    -- ^ Names can be specified in Z3 or in LaTeX encoding
    -- ^ They can then be rendered in either Z3 or LaTeX
    -- ^ by using `substToZ3` and `substToLatex` to translate them
data Name = Name 
        { _backslash :: !Bool 
        , _base :: !NEString 
        , _primes :: !Word8 
        , _suffix :: !String
        } deriving (Data,Generic,Eq,Ord,Show)

data InternalName = InternalName !String !Name !String
    deriving (Eq,Ord,Data,Generic,Show)

#endif

data Encoding = Z3Encoding | LatexEncoding
    deriving (Eq,Ord,Data,Generic,Show)

makeLenses ''Name

name :: Bool -> NEString
             -> Word8
             -> String
             -> Encoding
             -> Name
name bl base pr suff Z3Encoding = Name bl base pr suff
name bl base pr suff LatexEncoding = Name bl 
        (replaceAll' substToZ3 base) pr 
        (replaceAll substToZ3 suff)

instance PrettyPrintable Name where
    pretty = render

instance PrettyPrintable InternalName where
    pretty = render

class (Show a,Ord a,Hashable a,Data a) => IsBaseName a where
    render :: a -> String
    asInternal' :: a -> InternalName
    asName'  :: a -> Name
    fromString'' :: Pre => String -> a
    addPrime :: a -> a
    generateNames :: a -> [a]
    language :: Proxy a -> Language a
    texName :: Pre 
            => String -> a
    z3Name :: Pre 
           => String -> a

_Name :: IsName a => Prism' String a
_Name = prism' render (fmap fromName . isZ3Name')

--instance Show Name where
--    show = [printf|[%s]|] . render

--instance Show InternalName where
--    show x = [printf|{%s}|] $ render x


renderAsLatex :: Name -> String
renderAsLatex (Name b base' p suff') = concat [slash,toList base,replicate (fromIntegral p) '\'',suffix]
    where
        -- (Name b base p suff _) = toLatexEncoding n
        base = replaceAll' substToLatex base'
        suff = replaceAll substToLatex suff'

        slash  | b          = "\\"
               | otherwise  = ""
        suffix | L.null suff = ""
               | otherwise   = [printf|_{%s}|] suff

instance IsBaseName Name where
    render = renderAsLatex
    --asString arse = iso render $ makeName arse
    asInternal' n = InternalName "" n ""
    asName' = id
    fromString'' = makeName
    --addSuffix (Name n0) n1 = Name $ n0 <> ('@' :| n1)
    --dropSuffix (Name (n:|ns)) = Name $ n :| L.takeWhile ('@' /=) ns
    addPrime = primes %~ (+1)
    generateNames n = n : [ n & base %~ (<+ show i) | i <- [0..] ]
    language Proxy = latexName
    z3Name = fromJust' . isZ3Name'
    texName = fromString''

class IsBaseName n => IsName n where
    fromInternal :: InternalName -> n
    fromName :: Name -> n

asInternal :: IsName n => n -> InternalName
asInternal = asInternal'
--asInternal = view (from internal) . asInternal'

asName :: IsName n => n -> Name    
asName = asName'
--asName = view (from name) . asName'

instance IsName Name where
    fromInternal = asName
    fromName = id
instance IsName InternalName where
    fromInternal = id
    fromName = asInternal

fresh :: IsBaseName n => n -> Table n b -> n
fresh name xs = L.head $ ys `Ord.minus` M.ascKeys xs
    where
        ys = generateNames name

make :: (Pre,IsBaseName n0,IsBaseName n1)
     => (n0 -> n1 -> a)
     -> String -> String -> a
make f inm = make' (make' f inm)
    --f (fromString'' inm) (makeName (withCallStack assert) nm)

make' :: (Pre,IsBaseName n)
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
    render (InternalName pre x suf) = prefix ++ z3Render x ++ suf
        where
            prefix | null pre  = ""
                   | otherwise = [printf|@@%s@@_|] pre
            --suffix | null suf  = ""
            --       | otherwise = "@" ++ suf
    --asString arse = iso render $ fromString' arse
    asInternal' = id
    asName' (InternalName _ n _) = n
    fromString'' = fromString'
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

instance Hashable Name where
instance Hashable InternalName where
instance Hashable Encoding where

z3Render :: Name -> String
z3Render (Name sl xs ps suf) 
        = concat $ [slash,NE.toList xs] ++ replicate (fromIntegral ps) "@prime" ++ [suf']
    where
        slash | sl        = "sl$"
              | otherwise = ""
        suf'  | null suf  = ""
              | otherwise = "@" ++ suf

setSuffix :: String -> Name -> Name
setSuffix suff = suffix .~ suff

fromString' :: Pre => String -> InternalName
fromString' nm = InternalName "" (fromJust' $ isZ3Name' n) suf
    where
        (n,suf) = L.span ('@' /=) nm


isZ3Name' :: String -> Maybe Name
isZ3Name' x = either (const Nothing) Just $ isZ3Name x
    --parse z3Name' "" x

isZ3Name :: String -> Either [String] Name
isZ3Name str = mapLeft (\x -> [err,show x]) $ parse' z3Name' "" str
    where
        err = [printf|invalid name: '%s'|] str

isName :: String -> Either [String] Name
isName str = mapLeft (\x -> [err,show x]) $ parse' latexName "" str
    where
        err = [printf|invalid name: '%s'|] str

isName' :: String -> Maybe Name
isName' = either (const Nothing) Just . isName

makeZ3Name :: Pre => String -> Name
makeZ3Name = fromJust' . isZ3Name'

makeName :: Pre => String -> Name
makeName = fromJust' . isName'

addBackslash :: Name -> Name
addBackslash = backslash .~ True

addSuffix :: String -> InternalName -> InternalName
addSuffix n1 (InternalName pre n0 suf) = InternalName pre n0 $ suf ++ n1

dropSuffix :: InternalName -> InternalName
dropSuffix (InternalName pre ns _) = InternalName pre ns ""


reserved :: String -> Int -> InternalName
reserved pre n = InternalName pre (makeName $ show n) ""

internal :: Lens' InternalName Name
internal f (InternalName pre n suf) = (\n' -> InternalName pre n' suf) <$> f n
 
z3Name' :: Language Name
z3Name' = symb <|> name
    where
        name = 
            Name <$> option False (try (string "sl$" >> pure True)) 
                 <*> many1' (alphaNum <|> char '-')
                 <*> (fromIntegral.L.length 
                        <$> many (string "@prime"))
                 <*> pure ""
        symb = Name False . sconcat <$> many1' symbol <*> pure 0 <*> pure ""

latexName :: Language Name
latexName = symb <|> name'
    where
        name' = 
            name <$> option False (string "\\" >> pure True) 
                 <*> many1' (alphaNum <|> char '_')
                 <*> (fromIntegral.L.length 
                        <$> many (string "\'"))
                 <*> pure ""
                 <*> pure LatexEncoding
        symb = name False <$> symbol' 
                          <*> pure 0 
                          <*> pure ""
                          <*> pure LatexEncoding
        symbol' = symbol <|> texSymbol

texSymbol :: Language NEString
texSymbol = (:| []) <$> oneOf [';','.']

symbol :: Language NEString
symbol = ((:| []) <$> (oneOf ['-','*','/'] <|> satisfy isSymbol)) <?> "symbol"

data SubstPattern = SPat [(String,String)] [(String,String)] [(String,String)]
    deriving Show

inverse :: SubstPattern -> SubstPattern
inverse (SPat x y z) = SPat (L.map swap x) (L.map swap y) (L.map swap z)

substToZ3 :: SubstPattern
substToZ3 = SPat [("\\","sl$")] [] [("'","@prime")]

substToLatex :: SubstPattern
substToLatex = inverse substToZ3

shuffle' :: SubstPattern -> Gen SubstPattern
shuffle' (SPat x y z) = SPat <$> shuffle x <*> shuffle y <*> shuffle z

replaceAll' :: Pre 
            => SubstPattern -> NonEmpty Char -> NonEmpty Char
replaceAll' sub = nonEmpty' . replaceAll sub . toList

preSubtituted :: String -> (String,String) -> Maybe (String,String)
preSubtituted xs (pat,sub) = (sub,) <$> xs^?prefixed pat

postSubtituted :: String -> (String,String) -> Maybe (String,String)
postSubtituted xs (pat,sub) = (,sub) <$> xs^?suffixed pat

midSubtituted :: String -> (String,String) -> Maybe (String,String)
midSubtituted xs (pat,sub) = (_1 %~ (++ sub)) <$> xs^?foldSplits . below (prefixed pat)

foldSplits :: Fold [a] ([a],[a])
foldSplits = folding $ \xs -> L.zip (L.inits xs) (L.tails xs)

replaceAll :: SubstPattern -> String -> String
replaceAll (SPat pre mid suff) = substPre
    where
        substPre xs = fromMaybe (substPost xs) $ do
                (p,s) <- pre^?traverse.folding (preSubtituted xs)
                return $ p ++ substPre s
        substPost xs = fromMaybe (substMid xs) $ do
                (p,s) <- suff^?traverse.folding (postSubtituted xs)
                return $ substPost p ++ s
        substMid xs = fromMaybe xs $ do
                (p,s) <- mid^?traverse.folding (midSubtituted xs)
                return $ p ++ substMid s

smt :: QuasiQuoter
smt = QuasiQuoter
    { quoteExp  = \str -> [e| fromName $ $(parseZ3Name str) |]
    --{ quoteExp  = \str -> [e| fromName . view (from name) $ $(parseZ3Name str) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

tex :: QuasiQuoter
tex = QuasiQuoter
    { quoteExp  = \str -> [e| $(parseTexName str) |]
    --{ quoteExp  = \str -> [e| view (from name) $ $(parseTexName str) |]
    , quotePat  = undefined
    , quoteDec  = undefined
    , quoteType = undefined }

parseZ3Name :: String -> ExpQ
parseZ3Name str = either (fail . unlines) TH.lift $ isZ3Name str

parseTexName :: String -> ExpQ
parseTexName str = either (fail . unlines) TH.lift $ isName str

prop_subst_idempotent :: String -> Property
prop_subst_idempotent xs = replaceAll substToZ3 (replaceAll substToZ3 xs) === replaceAll substToZ3 xs

prop_rev_substToZ3_idempotent :: String -> Property
prop_rev_substToZ3_idempotent xs = replaceAll substToLatex (replaceAll substToLatex xs) === replaceAll substToLatex xs

prop_subst_order_independent :: String -> Property
prop_subst_order_independent xs = forAll (shuffle' substToZ3) $ \s -> replaceAll s xs === replaceAll substToZ3 xs

prop_rev_subst_order_independent :: String -> Property
prop_rev_subst_order_independent xs = forAll (shuffle' substToLatex) $ \s -> replaceAll s xs === replaceAll substToLatex xs

prop_subst_left_inv :: Name -> Property
prop_subst_left_inv xs = 
        replaceAll substToLatex (replaceAll substToZ3 $ render xs) === render xs

prop_subst_left_inv_regression :: Property
prop_subst_left_inv_regression = regression
        prop_subst_left_inv
        [ name0, name1, name2 ]

name0 :: Name
name0 = Name True ('s' :| "l") 1 ""

name1 :: Name
name1 = Name True ('p' :| "rime") 1 ""

name2 :: Name
name2 = Name {_backslash = False, _base = 's' :| "l", _primes = 1, _suffix = ""}

prop_subst_right_inv :: InternalName -> Property
prop_subst_right_inv xs = 
        replaceAll substToZ3 (replaceAll substToLatex $ render xs) === render xs

prop_subst_preserves_non_emptiness :: NonEmptyList Char -> Property
prop_subst_preserves_non_emptiness (NonEmpty xs) = replaceAll substToZ3 xs =/= []

prop_substToLatex_preserves_non_emptiness :: NonEmptyList Char -> Property
prop_substToLatex_preserves_non_emptiness (NonEmpty xs) = replaceAll substToLatex xs =/= []

prop_insertAt :: (Eq a,Show a) => Int -> [a] -> NonEmpty a -> Property
prop_insertAt n xs ys = NE.toList (insertAt n xs ys) === L.take n ys' ++ xs ++ L.drop n ys'
    where
        ys' = NE.toList ys

prop_render_isomorphic :: Name -> Name -> Property
prop_render_isomorphic xs ys = counterexample 
        (show (render xs) ++ "\n" ++ show (render ys))
        $ (render xs == render ys) === (xs == ys)

nonEmptyOf :: Gen a -> Gen (NonEmpty a)
nonEmptyOf gen = (:|) <$> gen <*> listOf gen

infix 4 =/=
(=/=) :: (Eq a, Show a) => a -> a -> Property
x =/= y = counterexample (show x ++ " == " ++ show y) (x /= y)

insertAt :: Int -> [a] -> NonEmpty a -> NonEmpty a
insertAt n xs ne@(y :| ys) 
    | n <= 0    = foldr (NE.<|) ne xs
    | otherwise = y :| (L.take (n-1) ys ++ xs ++ L.drop (n-1) ys)

instance Arbitrary Name where
    arbitrary = do
        r <- oneof 
            [ word latexName
            , word z3Name' ]
        let sl    = 's' :| "l"
            prime = 'p' :| "rime"
        oneof 
            [ do 
                n <- choose (0,3)
                let cmd n = do
                        i  <- QC.elements [0,NE.length $ n^.base]
                        kw <- QC.elements ["sl","prime"]
                        return $ ((),n & base %~ insertAt i kw)
                execStateT (replicateM_ n $ StateT cmd) r
            , r & base (const $ sconcat <$> nonEmptyOf (QC.elements [sl,prime])) ]

instance Arbitrary InternalName where
    arbitrary = do
        asInternal' <$> (arbitrary :: Gen Name)

instance TH.Lift Name where
    lift (Name a b c d) = [e| name a b c d Z3Encoding |]
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

class Translatable a b | a -> b where
    translate :: a -> b

return []

run_props :: (PropName -> Property -> IO (a, QC.Result))
          -> IO ([a], Bool)
run_props = $forAllProperties'
