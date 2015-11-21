module Document.Phase.Parameters where

    -- Modules
--import Document.Phase

import Latex.Parser

import Logic.Expr

import UnitB.AST

    -- Libraries
import Data.Char
import Data.String
import Data.String.Utils

import Utilities.Syntactic

newtype TheoryName = TheoryName {getTheoryName :: String}

newtype RuleName = RuleName String

newtype VarName = VarName { getVarName :: String }

newtype SetName = SetName { getSetName :: String }

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

comma_sep :: String -> [String]
comma_sep [] = []
comma_sep xs = trim ys : comma_sep (drop 1 zs)
    where
        (ys,zs) = break (== ',') xs

trim :: [Char] -> [Char]
trim xs = reverse $ f $ reverse $ f xs
    where
        f = dropWhile isSpace

class LatexArgFromString a where
    readFromString :: String -> a

class LatexArg a where
    read_one :: LatexDoc -> Either [Error] a
    default read_one :: LatexArgFromString a => LatexDoc -> Either [Error] a
    read_one = read_one'

read_one' :: LatexArgFromString a => LatexDoc -> Either [Error] a
read_one' = fmap readFromString . readString

--class LatexArg a where
--    read_one' :: LatexDoc -> Either [Error] a
--    read_one' = fmap readFromString . readString

instance LatexArg TheoryName where
instance LatexArgFromString TheoryName where
    readFromString = TheoryName

instance LatexArg MachineId where
instance LatexArgFromString MachineId where
    readFromString = MId

instance LatexArg RuleName where
instance LatexArgFromString RuleName where
    readFromString = RuleName

instance LatexArg ProgId where
instance LatexArgFromString ProgId where
    readFromString = PId . label

instance LatexArg VarName where
instance LatexArgFromString VarName where
    readFromString = VarName . strip

instance LatexArg SetName where
instance LatexArgFromString SetName where
    readFromString = SetName

instance LatexArgFromString EventId where
    readFromString = fromString

instance LatexArg ExprText where
    read_one = return . Expr . flatten_li' . trim_blank_text'

instance LatexArgFromString CoarseSchLbl where
    readFromString = CoarseSchLbl . fromString

instance LatexArgFromString FineSchLbl where
    readFromString = FineSchLbl . fromString

instance LatexArgFromString ActionLbl where
    readFromString = ActionLbl . fromString

instance LatexArgFromString GuardLbl where
    readFromString = GuardLbl . fromString

instance LatexArgFromString InitLbl where
    readFromString = InitLbl . fromString

instance LatexArg PO where
    read_one = return . PO . flatten
instance LatexArgFromString PO where
    readFromString = PO

instance LatexArg NewLabel where
instance LatexArgFromString NewLabel where
    readFromString = NewLabel . fromString

instance LatexArg PlainText where
    read_one = return . PlainText

instance LatexArgFromString a => LatexArgFromString (Conc a) where
    readFromString = Conc . readFromString
instance LatexArgFromString a => LatexArgFromString (Abs a) where
    readFromString = Abs . readFromString
instance LatexArgFromString a => LatexArgFromString (Common a) where
    readFromString = Common . readFromString
instance LatexArgFromString a => LatexArg (Conc a) where
instance LatexArgFromString a => LatexArg (Abs a) where
instance LatexArgFromString a => LatexArg (Common a) where
instance LatexArgFromString a => LatexArg [a] where
    read_one = return . (map readFromString . comma_sep) . flatten

newtype Abs a = Abs { getAbstract :: a }
    deriving (Eq,Ord)

newtype Conc a = Conc { getConcrete :: a }
    deriving (Eq,Ord)

newtype Common a = Common { getCommon :: a }
    deriving (Eq,Ord)
