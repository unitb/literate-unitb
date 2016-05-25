module Logic.UnitTest where

    -- Modules
import Logic.Expr hiding ( name )
import Logic.Proof

import Z3.Z3

    -- Libraries
import Control.Applicative
import Control.Exception
import Control.Lens hiding ((<.>))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Precondition

import           Data.List
import qualified Data.Map.Class as M
import           Data.Tuple

import GHC.Stack

import Prelude

import Utilities.Table

import System.IO

import Test.UnitTest

import Text.Printf.TH

data POCase = POCase String (IO (String, Table Label Sequent)) String

poCase :: String 
       -> IO (String, Table Label Sequent) 
       -> String
       -> TestCase
poCase n test res = Other $ POCase n test res

instance IsTestCase POCase where
    makeCase cs (POCase n test res)     = do
            let cmd = catch (test & mapped._2 %~ print_po) handler
                handler exc = do
                    putStrLn "*** EXCEPTION ***"
                    putStrLn n
                    print exc
                    return (show (exc :: SomeException), logNothing)
                -- get_po = catch (snd `liftM` y) g
                -- g :: SomeException -> IO (Table Label Sequent)
                -- g = const $ putStrLn "EXCEPTION!!!" >> return M.empty
            return UT
                { name = n
                , routine = cmd
                , outcome = res
                , _mcallStack = cs
                , _displayA = id
                , _displayE = id
                , _criterion = id
                }
    nameOf f (POCase n test res) = (\n' -> POCase n' test res) <$> f n

print_po :: Table Label Sequent -> CallStack -> String -> String -> String -> M ()
print_po pos cs name actual expected = do
    n <- get
    liftIO $ do
        let ma = f actual
            me = f expected
            f :: String -> Table String Bool
            f xs = M.map (== "  o  ") $ M.fromList $ map (swap . splitAt 5) $ lines xs
            mr = M.keys $ M.filter not $ M.unionWith (==) (me `M.intersection` ma) ma
        forM_ (zip [0..] mr) $ \(i,po) -> do
            if label po `M.member` pos then do
                withFile ([printf|po-%d-%d.z3|] n i) WriteMode $ \h -> do
                    hPutStrLn h $ "; " ++ name
                    hPutStrLn h $ "; " ++ po
                    hPutStrLn h $ "; " ++ if not $ ma ! po 
                                          then  "does {not discharge} automatically"
                                          else  "{discharges} automatically"
                    forM_ (callStackLineInfo cs) $ hPutStrLn h . ("; " ++)
                    hPutStrLn h $ unlines $ z3_code (pos ! label po) : ["; " ++ po]
            else return ()
