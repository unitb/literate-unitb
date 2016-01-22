{-# LANGUAGE KindSignatures #-}
module Utilities.Language where

import Control.Lens hiding (elements)
import Control.Monad
import Control.Monad.Writer hiding ((<>))

import Data.Char
import Data.List.NonEmpty
import Data.Semigroup hiding (option)

import qualified Text.Parsec as P

import Test.QuickCheck as QC

newtype Language a = Language { _language :: forall m. IsLanguage m => m a}
    deriving (Functor)

class (Monad m) => IsLanguage (m :: * -> *) where
    (<?>) :: m a -> String -> m a
    (<|>) :: m a -> m a -> m a
    anyChar :: m Char
    string :: String -> m String
    many1 :: m a -> m [a]
    many  :: m a -> m [a]
    option :: a -> m a -> m a
    alphaNum :: m Char
    char :: Char -> m Char
    suchThat :: (a -> Bool) -> m a -> m a
    oneOf :: [Char] -> m Char
    satisfy :: (Char -> Bool) -> m Char
    try :: m a -> m a

makeLenses ''Language

--instance Alternative Language where
--instance MonadPlus Language where
instance Applicative Language where
    pure = return
    (<*>) = ap
instance Monad Language where
    return x = Language $ return x
    Language x >>= f = Language $ x >>= _language . f

newtype Gen' a = Gen { getGen :: Gen (NonEmpty (Writer String a)) }
    deriving (Functor)

elements' :: NonEmpty a -> Gen a
elements' = elements . toList

oneof' :: NonEmpty (Gen a) -> Gen a
oneof' = oneof . toList

--instance MonadPlus Gen' where
--instance Alternative Gen' where
instance Applicative Gen' where
    pure = return
    (<*>) = ap
instance Monad Gen' where
    return x = Gen $ return $ (return x) :| []
    Gen xs >>= f = Gen $ do
            (r,w) <- runWriter <$> (elements' =<< xs)
            fmap (fmap (tell w >>)) . getGen . f $ r

instance IsLanguage (P.Parsec [Char] ()) where
    (<?>) = (P.<?>)
    (<|>) = (P.<|>)
    anyChar = P.anyChar
    string  = P.string
    many1  = P.many1
    many   = P.many
    option = P.option
    alphaNum = P.alphaNum
    oneOf = P.oneOf
    char  = P.char
    satisfy = P.satisfy
    try     = P.try
    suchThat p cmd = cmd >>= (\x -> guard (p x) >> return x)

ne :: a -> NonEmpty a
ne = (:| [])

ne' :: Char -> NonEmpty (Writer String Char)
ne' x = (tell [x] >> return x) :| []

instance IsLanguage Gen' where
    (<?>) = const
    Gen xs <|> Gen ys = Gen $ (<>) <$> xs <*> ys
    anyChar = Gen $ ne' <$> arbitrary
    string str = Gen $ return $ ne $ tell str >> return str
    many1 (Gen cmd) = Gen $ fmap sequence . ne <$> listOf1 (elements' =<< cmd)
    many (Gen cmd)  = Gen $ fmap sequence . ne <$> listOf (elements' =<< cmd)
    option x cmd = return x <|> cmd
    alphaNum = Gen $ fmap ne' $ QC.suchThat arbitrary isAlphaNum
    oneOf xs = Gen $ fmap sconcat $ sequence $ fmap (getGen . char) (fromList xs)
    satisfy p = Gen $ fmap ne' $ QC.suchThat arbitrary p
    suchThat p (Gen x) = Gen $ fmap ne $ flip QC.suchThat (p . fst . runWriter) (elements' =<< x) 
    char c = Gen $ return $ ne' c
    try cmd = cmd

instance IsLanguage Language where
    Language x <?> tag = Language $ x <?> tag
    Language x <|> Language y = Language $ x <|> y
    anyChar  = Language anyChar
    string x = Language $ string x
    option x (Language cmd) = Language $ option x cmd
    many1 (Language cmd) = Language $ many1 cmd
    many (Language cmd)  = Language $ many cmd
    alphaNum = Language $ alphaNum
    oneOf cs = Language $ oneOf cs
    satisfy p = Language $ satisfy p
    char c    = Language $ char c
    try (Language cmd) = Language $ try cmd
    suchThat p (Language cmd) = Language $ Utilities.Language.suchThat p cmd

many1' :: Language a -> Language (NonEmpty a)
many1' cmd = (:|) <$> cmd <*> many cmd

parse :: Language a -> P.SourceName -> String -> Maybe a
parse cmd src xs = either (const Nothing) Just $ parse' cmd src xs

parse' :: Language a -> P.SourceName -> String -> Either P.ParseError a
parse' (Language cmd) = P.parse (cmd >>= \x -> P.eof >> return x)

gen :: Language a -> Gen String
gen (Language (Gen cmd)) = fmap execWriter $ elements' =<< cmd

word :: Language a -> Gen a
word (Language (Gen cmd)) = fmap (fst . runWriter) $ elements' =<< cmd

--    Not in scope: ‘<?>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<.>’ (imported from Control.Lens)

--    Not in scope: ‘<|>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<|’ (imported from Control.Lens)

--    Not in scope: ‘<?>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<.>’ (imported from Control.Lens)

--    Not in scope: ‘anyChar’

--    Not in scope: ‘<?>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<.>’ (imported from Control.Lens)

--    Not in scope: ‘option’
--    Perhaps you meant data constructor ‘Option’ (imported from Data.Semigroup)

--    Not in scope: ‘string’
--    Perhaps you meant one of these:
--      ‘string'’ (line 202), ‘storing’ (imported from Control.Lens),
--      ‘strict’ (imported from Control.Lens)

--    Not in scope: ‘alphaNum’

--    Not in scope: ‘<|>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<|’ (imported from Control.Lens)

--    Not in scope: ‘option’
--    Perhaps you meant data constructor ‘Option’ (imported from Data.Semigroup)

--    Not in scope: ‘string’
--    Perhaps you meant one of these:
--      ‘string'’ (line 202), ‘storing’ (imported from Control.Lens),
--      ‘strict’ (imported from Control.Lens)

--    Not in scope: ‘alphaNum’

--    Not in scope: ‘<|>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<|’ (imported from Control.Lens)

--    Not in scope: ‘oneOf’
--    Perhaps you meant one of these:
--      ‘noneOf’ (imported from Control.Lens),
--      ‘oneof’ (imported from Test.QuickCheck)

--    Not in scope: ‘many’
--    Perhaps you meant one of these:
--      ‘any’ (imported from Data.List),
--      ‘iany’ (imported from Control.Lens)

--    Not in scope: ‘oneOf’
--    Perhaps you meant one of these:
--      ‘noneOf’ (imported from Control.Lens),
--      ‘oneof’ (imported from Test.QuickCheck)

--    Not in scope: ‘<|>’
--    Perhaps you meant one of these:
--      ‘<*>’ (imported from Prelude), ‘<$>’ (imported from Prelude),
--      ‘<|’ (imported from Control.Lens)

--    Not in scope: ‘satisfy’
