module Text.Printf.TH where

import Text.Printf as P
import Language.Haskell.TH
import Language.Haskell.TH.Quote

printf :: QuasiQuoter
printf = QuasiQuoter
    { quoteExp  = \str -> [e|P.printf $(stringE =<< unescape str) :: $(typeOf str)|] 
    , quoteType = undefined 
    , quotePat  = undefined 
    , quoteDec  = undefined }

unescape :: String -> Q String
unescape ('\\':'\\':xs) = ('\\' :) <$> unescape xs
unescape ('\\':'\"':xs) = ('\"' :) <$> unescape xs
unescape ('\\':'n':xs)  = ('\n' :) <$> unescape xs
unescape ('\\':'t':xs)  = ('\t' :) <$> unescape xs
unescape ('\\':_)       = fail "invalid escape character"
unescape (c:cs)         = (c :) <$> unescape cs
unescape []             = pure []

typeOf :: String -> TypeQ
typeOf [] = [t|String|]
typeOf ('%':'s':xs) = [t| String -> $(typeOf xs) |]
typeOf ('%':'d':xs) = [t| Int -> $(typeOf xs) |]
typeOf ('%':'%':xs) = typeOf xs
typeOf ('%':c:_)      = error $ "invalid escape character: %" ++ [c]
typeOf ('%':_)      = error $ "invalid escape character: %"
typeOf (_:cs)       = typeOf cs

subst :: String -> Int -> String -> String
subst [] _ _ = []
subst xs n z
        | take m xs == fn   = z ++ subst (drop m xs) n z
        | otherwise         = take 1 xs ++ subst (drop 1 xs) n z
    where
        fn = "{" ++ show n ++ "}"
        m = length fn

substAll :: String -> [String] -> String
substAll xs ys = foldl (uncurry <$> subst) xs $ zip [0..] ys
