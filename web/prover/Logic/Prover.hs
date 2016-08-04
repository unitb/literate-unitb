module Logic.Prover where

import           Logic.Expr hiding ( (</>) )
import           Logic.Expr.Printable
import           Logic.Proof.Monad
import qualified Logic.Proof.Sequent as S
import           Logic.Theories
import           Logic.Theories.IntervalTheory (interval_theory)
import           Logic.Theory
import           TeX2PNG
import           Utilities.Syntactic
import qualified Z3.Z3 as Z3

import           Control.Lens
import           Control.Precondition
import qualified Data.Map as M
import           Data.Maybe
import           System.Directory
import           System.FilePath

import           Import

import           Model.ProofForm
import           Model.ProofResult

pfStringToPfStringLi :: ProofForm String -> ProofForm StringLi
pfStringToPfStringLi p@(ProofForm _ d a g) =
    p { declarations = d & traverse %~ (\(lbl,decl) -> (lbl, toSringLi lbl decl))
      , assumptions  = a & traverse._2 %~ (\(lbl,asm)  -> (lbl, toSringLi lbl asm))
      , goal = toSringLi "goal" g
    }

pfStringLiToSequent :: ProofForm StringLi -> Either [Error] DispSequentWithWD
pfStringLiToSequent (ProofForm t d a g) = runSequent $ do
    let theories = getTheories t
    mapM_ include  theories
    mapM_ declareE (map snd d)
    mapM_ assumeE  (map snd a)
    checkE' g

discharge :: Either [Error] DispSequentWithWD -> IO ProofResult
discharge e = do
    cur <- getCurrentDirectory  -- project root
    let imgPath = "static" </> "img"
        imgDir = cur </> imgPath
    case e of
        Left err ->
            return $ ProofResult { _result = Left err, _goalPng = "" }
        Right s -> do
            p <- mkPNG $ args (pack . getLatex $ _goal s) imgDir
            let pngFullPath = either unpack id p
                pngPath = imgPath </> (snd . splitFileName $ pngFullPath)
            val <- Z3.dischargeBoth "goal" s
            return $ ProofResult { _result = Right val, _goalPng = pngPath }
  where
    args c d = Args "transparent" c (Just d) 150 False True Nothing 1 packages Nothing True
    packages = Just $ pack <$> ["bsymb", "calculation", "eventB", "unitb"]
    getLatex sequent = concat
                       [ "& \\hspace{-4pt} \\begin{array}{l@{\\quad}l}\n"
                       , foldr
                         (\(lbl, expr) accum -> concat
                           [ "\\textsf{"
                           , pretty lbl
                           , "}: & "
                           , prettyPrint expr
                           , " \\\\\n"
                           , accum
                           ])
                         ""
                         . M.toList $ sequent^.(S.named)
                       , "\\end{array}\n"
                       , "\\\\[-0.25cm]\n"
                       , "\\vdash & \\\\[-0.25cm]\n"
                       , "& ", prettyPrint $ sequent^.(S.goal)
                       ]

prove :: ProofForm String -> IO ProofResult
prove = discharge . pfStringLiToSequent . pfStringToPfStringLi

getTheories :: Vector String -> Vector Theory
getTheories = fromList . concat . map getTheory

getTheory :: Pre => String -> [Theory]
getTheory str@"arithmetic" =
    (fromJust . M.lookup (makeName str) $ supportedTheories)
    : interval_theory : []
getTheory str = (fromJust . M.lookup (makeName str) $ supportedTheories) : []

toSringLi :: String -> String -> StringLi
toSringLi lbl = asStringLi . mkLI $ lbl
