module Logic.Expr.Prism 
    ( module Logic.Names 
    -- , module Record 
    , fun )
where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Expr
import Logic.Names

    -- Libraries
import Control.Lens hiding (uncons)

import Data.Functor.Contravariant
import Data.List.Lens
import Data.Maybe
import Data.String.Utils

import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.Quote

import Utilities.TH

fun :: QuasiQuoter
fun = QuasiQuoter 
        { quoteExp  = funPrism . makePattern
        , quoteType = undefined
        , quotePat  = funPat
        , quoteDec  = undefined }

{-# INLINE selectFun #-}
selectFun :: Eq n => n -> Traversal' (AbsFun n t,[GenExpr n t a q]) [GenExpr n t a q]
selectFun fn f (fn',args') | fn == (fn'^.name) = (fn',) <$> f args'
                           | otherwise         = pure (fn',args')

zipRecord' :: [Maybe String] -> ExpQ
zipRecord' args = 
        [e| filtered (($recSize ==) . length) . (\f _args -> phantom $ f $(myLet)) :: Fold [GenExpr n t a q] $(recType) |]
    where
        recSize = litE $ integerL $ fromIntegral $ length fieldPos
        decs = map (binding . snd) fieldPos
        decs :: [DecQ]
        binding n = valD (varP $ mkName $ "x" ++ show n) 
                         (normalB [e| $(varE $ mkName "_args") !! $(litE $ integerL $ fromIntegral n) |]) []
        myLet = letE decs $ tupE [ varE (mkName $ "x" ++ show i) | (_,i) <- fieldPos ]
        fieldPos = mapMaybe (sequenceOf _1) $ zip args [0..]
        (n,t,a,q) = ("n","t","a","q") & each %~ (varT . mkName)
        recType  = appsT $ tupleT (length fieldPos) : replicate (length fieldPos) [t| GenExpr $n $t $a $q |]

funPrism :: Pattern -> ExpQ 
funPrism (Pattern f args) = [e| _FunApp . selectFun (fromName f) . $(zipRecord' args) |]

fieldTuple :: [String] -> PatQ
fieldTuple kw = tupP $ map (varP . mkName) kw

tuplePrism :: Pattern -> PatQ
tuplePrism (Pattern _ args) = [p| Just $(fieldTuple $ catMaybes args) |]

data Pattern = Pattern Name [Maybe String]

makePattern :: String -> Pattern
makePattern str = Pattern kw' args''
    where
        inside = fromMaybe (error "expecting parenthesis around S-expression")
                    $ strip str^?prefixed "(".suffixed ")"
        (kw,args) = fromMaybe (error "expecting at least one keyword")
                    $ inside^?partsOf worded._Cons
        args' = fromMaybe (error "field names should start with '$'")
                    $ args^?below (prefixed "$")
        kw' :: Name
        kw' = either (error . unlines) id $ isZ3Name kw
        args'' = map (^? filtered (/= "_")) args'

funPat :: String -> PatQ
funPat str = viewP 
        [e| preview $(funPrism pat) |] 
        (tuplePrism pat)
    where
        pat = makePattern str
