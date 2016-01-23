
import Control.Monad

import Data.Char
import Data.List

import System.Environment

main = do
    [fn] <- getArgs
    let eq x y = any isSpace $ take 1 y
    xs <- (map unlines . groupBy eq . lines) `liftM` readFile fn
    let assert x = "(assert " `isPrefixOf` x
        eq' x y = all assert [x,y]
        ys = map reverse $ groupBy eq' xs
    writeFile "po.z3" $ concat $ map concat ys
