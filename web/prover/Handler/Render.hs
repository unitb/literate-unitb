module Handler.Render where

import           Control.Lens
import           Data.Text (stripEnd)
import qualified Data.Vector as V
import           Logic.Expr hiding ((</>),Value)
import           Logic.Proof.Monad
import           System.Directory
import           System.FilePath
import           TeX2PNG
import           Utilities.Syntactic

import           Import
import           Logic.Prover
import           Logic.Utilities
import           Model.ProofForm

postRenderR :: Handler Value
postRenderR = do
  cur <- lift getCurrentDirectory  -- project root
  let imgPath = "static" </> "img"
      imgDir = cur </> imgPath
  content <- requireJsonBody :: Handler (Text)
  p <- lift $ mkPNG $ args content imgDir
  let pngFullPath = either unpack id p
      pngPath = imgPath </> (snd . splitFileName $ pngFullPath)
  returnJson pngPath
  where
    args c d = Args "transparent" c (Just d) 150 False True Nothing 1 packages Nothing True
    packages = Just $ pack <$> ["bsymb", "eventB", "unitb", "calculational"]


postRenderFormR :: Handler Value
postRenderFormR = do
  cur <- lift getCurrentDirectory  -- project root
  let imgPath = "static" </> "img"
      imgDir = cur </> imgPath
  form <- requireJsonBody :: Handler (ProofForm Text)
  p <- lift $ mkPNG $ args (getLatex form) imgDir
  let pngFullPath = either unpack id p
      pngPath = imgPath </> (snd . splitFileName $ pngFullPath)
  returnJson pngPath
  where
    args c d = Args "transparent" c (Just d) 150 False True Nothing 1 packages Nothing True
    packages = Just $ pack <$> ["bsymb", "eventB", "unitb", "calculational"]
    getLatex :: ProofForm Text -> Text
    getLatex form = intercalate "\n"
                    [ "& \\ \\boxed{"
                    , "\\begin{array}{ll}"
                    , "\\textsf{using} \\\\"
                    , "\\quad " <> "\\textit{" <> theories' <> "} \\\\"
                    , "\\textsf{variables} \\\\"
                    , "\\quad " <> declarations'
                    , "\\end{array}"
                    , "}\\\\[0.75em]"
                    , "& \\begin{array}{l@{\\quad}l}"
                    , assumptions'
                    , "\\end{array}"
                    , "\\\\[-0.5em]"
                    , "\\vdash & \\\\[-0.5em]"
                    , "& \\ " <> goal'
                    ]
      where
        theories' = intercalate ", " $ pack <$> form^.theories
        declarations' = intercalate " & \\\\\n\\quad " $
                        intercalate "\n" <$>
                        decls (form^.theories) (form^.declarations)
        assumptions' = stripEnd . assums $ form^.assumptions
        goal' = form^.goal

    decls :: Vector String -> Vector (String, Text) -> [[Text]]
    decls ts ds = do
      let parsedDecls :: [Either [Error] [(Name,Var)]]
          parsedDecls = V.toList $ parseDeclarations (toList $ getTheories ts)
                        <$> (\(declName, decl) -> toStringLi declName (unpack decl))
                        <$> ds
      runDecl <$> parsedDecls
      where
        runDecl = either (\errs -> [pack $ show_err errs]) (fmap (pack . varDecl . snd))

    assums :: Vector (String, (String, Text)) -> Text
    assums as = foldr (\(_, (lbl, asm)) accum -> concat
                        [ "\\textsf{" , pack lbl, "}: & ", asm, " \\\\\n", accum ])
                "" . toList $ as
