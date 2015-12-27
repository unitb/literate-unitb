module Document.Phase.Parameters where

    -- Modules
import Latex.Parser

import Logic.Expr

import UnitB.Syntax

    -- Libraries
import Data.Char
import Data.Either.Validation
import Data.String
import Data.String.Utils
import Data.Proxy

import Utilities.Syntactic

newtype TheoryName = TheoryName { getTheoryName :: Name }

newtype RuleName = RuleName String

newtype VarName = VarName { getVarName :: Name }

newtype SetName = SetName { getSetName :: Name }

newtype ExprText = Expr { getExprText :: StringLi }

newtype PlainText = PlainText { getPlainText :: LatexDoc }

newtype PO = PO { getPO :: String }

newtype CoarseSchLbl = CoarseSchLbl { getCoarseSchLbl :: Label }

newtype FineSchLbl = FineSchLbl { getFineSchLbl :: Label }

newtype GuardLbl = GuardLbl { getGuardLbl :: Label }

newtype ActionLbl = ActionLbl { getActionLbl :: Label }

newtype InitLbl = InitLbl { getInitLbl :: Label }

newtype NewLabel = NewLabel { getNewLabel :: Label }

--type M = Either [Error]

readString :: LatexDoc -> Either [Error] String
readString x = do
        let x' = trim_blank_text' x
        case asSingleton x' of
            Just (Text (TextBlock x _))
                -> Right x
            Just (Text (Command x _))
                -> Right x
            _   -> err_msg x'
    where
        err_msg x = Left [Error "expecting a word" $ line_info x]

readName :: LineInfo -> String -> Either [Error] Name
readName li str' = do
    let str = strip str'
    with_li li $ isName str

comma_sep :: String -> [String]
comma_sep [] = []
comma_sep xs = trim ys : comma_sep (drop 1 zs)
    where
        (ys,zs) = break (== ',') xs

trim :: [Char] -> [Char]
trim xs = reverse $ f $ reverse $ f xs
    where
        f = dropWhile isSpace

readFromString :: (String -> a) -> LineInfo -> String -> Either [Error] a
readFromString f _ = return . f

class LatexArgFromString a where
    kind' :: Proxy a -> String
    read_one' :: LineInfo -> String -> Either [Error] a

class LatexArg a where
    argKind :: Proxy a -> String
    default argKind :: LatexArgFromString a => Proxy a -> String
    argKind = kind'
    read_one :: LatexDoc -> Either [Error] a
    default read_one :: LatexArgFromString a => LatexDoc -> Either [Error] a
    read_one doc = read_one' (line_info doc) =<< readString doc


instance LatexArg TheoryName where
instance LatexArgFromString TheoryName where
    kind' Proxy = "theory-name"
    read_one' li = fmap TheoryName . readName li

instance LatexArg MachineId where
instance LatexArgFromString MachineId where
    kind' Proxy = "machine-name"
    read_one' li = fmap MId . readName li

instance LatexArg RuleName where
instance LatexArgFromString RuleName where
    kind' Proxy = "rule"
    read_one' = readFromString RuleName

instance LatexArg ProgId where
instance LatexArgFromString ProgId where
    kind' Proxy = "progress-property-label"
    read_one' = readFromString $ PId . label

instance LatexArg VarName where
instance LatexArgFromString VarName where
    kind' Proxy = "variable"
    read_one' li = fmap VarName . readName li

instance LatexArg SetName where
instance LatexArgFromString SetName where
    kind' Proxy = "set-name"
    read_one' li = fmap SetName . readName li

instance LatexArgFromString EventId where
    kind' Proxy = "event-name"
    read_one' = readFromString $ fromString

instance LatexArg ExprText where
    argKind Proxy = "expression"
    read_one = return . Expr . flatten_li' . trim_blank_text'

instance LatexArgFromString CoarseSchLbl where
    kind' Proxy = "coarse-schedule-label"
    read_one' = readFromString $ CoarseSchLbl . fromString

instance LatexArgFromString FineSchLbl where
    kind' Proxy = "fine-schedule-label"
    read_one' = readFromString $ FineSchLbl . fromString

instance LatexArgFromString ActionLbl where
    kind' Proxy = "action-label"
    read_one' = readFromString $ ActionLbl . fromString

instance LatexArgFromString GuardLbl where
    kind' Proxy = "guard-label"
    read_one' = readFromString $ GuardLbl . fromString

instance LatexArgFromString InitLbl where
    kind' Proxy = "initialization-label"
    read_one' = readFromString $ InitLbl . fromString

instance LatexArg PO where
    read_one = return . PO . flatten
instance LatexArgFromString PO where
    kind' Proxy = "proof-obligation-name"
    read_one' = readFromString $ PO

instance LatexArg NewLabel where
instance LatexArgFromString NewLabel where
    kind' Proxy = "fresh-name"
    read_one' = readFromString $ NewLabel . fromString

instance LatexArg PlainText where
    argKind Proxy = "text / comment"
    read_one = return . PlainText

instance LatexArgFromString a => LatexArgFromString (Conc a) where
    read_one' li = fmap Conc . read_one' li
    kind' p = "concrete " ++ kind' (getConcrete <$> p)
instance LatexArgFromString a => LatexArgFromString (Abs a) where
    read_one' li = fmap Abs . read_one' li
    kind' p = "abstract " ++ kind' (getAbstract <$> p)
instance LatexArgFromString a => LatexArgFromString (Common a) where
    read_one' li = fmap Common . read_one' li
    kind' p = "preserved " ++ kind' (getCommon <$> p)
instance LatexArgFromString a => LatexArg (Conc a) where
    argKind p = "concrete " ++ kind' (getConcrete <$> p)
instance LatexArgFromString a => LatexArg (Abs a) where
    argKind p = "abstract " ++ kind' (getAbstract <$> p)
instance LatexArgFromString a => LatexArg (Common a) where
    argKind p = "preserved " ++ kind' (getCommon <$> p)
instance LatexArgFromString a => LatexArg [a] where
    argKind p = "zero or more " ++ kind' (head <$> p)
    read_one doc = validationToEither $ parseAll $ comma_sep $ flatten doc
        where 
            parseAll = traverse (eitherToValidation . read_one' (line_info doc))

newtype Abs a = Abs { getAbstract :: a }
    deriving (Eq,Ord)

newtype Conc a = Conc { getConcrete :: a }
    deriving (Eq,Ord)

newtype Common a = Common { getCommon :: a }
    deriving (Eq,Ord)
