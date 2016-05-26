{-# LANGUAGE CPP, QuasiQuotes, TemplateHaskell #-}
module Test.QuickCheck.Report where

import Control.Arrow
import Control.Lens
import Control.Lens.Extras
import Control.Monad

import Data.Char
import Data.IORef
import Data.List as L

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import qualified System.IO as S

import Test.QuickCheck
import Test.QuickCheck.Lens

import Text.Printf.TH

data PropName = PropName String FilePath Int

propDesc :: PropName -> String
propDesc (PropName x filename l) = x ++ " from " ++ filename ++ ":" ++ show l

quickCheckWithResult' :: Testable prop
                      => Args 
                      -> PropName
                      -> prop 
                      -> IO (String,Result)
quickCheckWithResult' args name prop = do
        r <- quickCheckWithResult args { chatty = False } prop
        return ([printf|=== %s ===\n%s\n|] (propDesc name) (output r),r)

quickCheckResult' :: Testable prop 
                  => PropName 
                  -> prop 
                  -> IO (String,Result)
quickCheckResult' = quickCheckWithResult' stdArgs


printQuickCheckResult :: Testable prop
                      => ((PropName -> prop -> IO (String,Result)) -> IO ([String],Bool))
                      -> IO ()
printQuickCheckResult = printQuickCheckWithResult stdArgs

printQuickCheckWithResult :: Testable prop
                          => Args
                          -> ((PropName -> prop -> IO (String,Result)) -> IO ([String],Bool))
                          -> IO ()
printQuickCheckWithResult args prop = prop (quickCheckWithResult' args) 
                                  >>= _1 (mapM_ putStrLn) 
                                  >>= _2 print
                                  >> return ()

quickCheckWrap :: Name -> ExpQ -- (PropName -> prop -> IO (a,Result)) -> IO ([a],Bool)
quickCheckWrap name = do
        loc <- location
        let name' = lift $ nameBase name
            fn    = lift $ loc_filename loc
            ln    = lift $ fst $ loc_start loc
            propName = [| PropName $name' $fn $ln |]
            prop  = monomorphic name
        [e| \check -> ((:[]) *** is _Success) <$> check $propName (property $prop) |]

forAllProperties' :: ExpQ -- :: (String -> Property -> IO (a,Result)) -> IO ([a],Bool)
forAllProperties' = do
  Loc { loc_filename = filename } <- location
  when (filename == "<interactive>") $ error "don't run this interactively"
  ls <- runIO (fmap lines (readUTF8File filename))
  let prefixes = L.map (takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') . dropWhile (\c -> isSpace c || c == '>')) ls
      idents = nubBy (\x y -> snd x == snd y) (L.filter (("prop_" `isPrefixOf`) . snd) (zip [1..] prefixes))
#if __GLASGOW_HASKELL__ > 705
      warning x = reportWarning ("Name " ++ x ++ " found in source file but was not in scope")
#else
      warning x = report False ("Name " ++ x ++ " found in source file but was not in scope")
#endif
      quickCheckOne :: (Int, String) -> Q [Exp]
      quickCheckOne (l, x) = do
        exists <- (warning x >> return False) `recover` (reify (mkName x) >> return True)
        if exists then sequence [ [| ( PropName x filename l
                                     , property $(monomorphic (mkName x))) |] ]
         else return []
  [| runQuickCheckAll' $(fmap (ListE . concat) (mapM quickCheckOne idents)) |]

readUTF8File :: FilePath -> IO String
readUTF8File name = S.openFile name S.ReadMode >>=
                    set_utf8_io_enc >>=
                    S.hGetContents

-- Deal with UTF-8 input and output.
set_utf8_io_enc :: S.Handle -> IO S.Handle
#if __GLASGOW_HASKELL__ > 611
-- possibly if MIN_VERSION_base(4,2,0)
set_utf8_io_enc h = do S.hSetEncoding h S.utf8; return h
#else
set_utf8_io_enc h = return h
#endif

runQuickCheckAll' :: [(PropName, Property)] 
                  -> (PropName -> Property -> IO (a,Result)) 
                  -> IO ([a],Bool)
runQuickCheckAll' ps qc = 
  fmap (L.map fst &&& all snd) . forM ps $ \(xs, p) -> do
    qc xs p & mapped._2 %~ is _Success
    -- return $ (x,is _Success r)

test_report :: Testable a
            => ((a -> IO Result) -> IO b) -> IO Bool
test_report tests = do 
    success <- newIORef (0 :: Int)
    total   <- newIORef (0 :: Int)
    let inc r = do
            when (is _Success r) 
                $ modifyIORef success (+1)
            modifyIORef total (+1)
            return r
    (tests $ (>>= inc) . quickCheckWithResult stdArgs {chatty = False})
    x <- readIORef success
    y <- readIORef total
    putStr $ [printf|success: %d / %d\n[ %s ]\n|]
        x y
        (if x == y then "passed" else "failed")
    return $ x == y
