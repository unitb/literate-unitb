#!/usr/bin/env runhaskell
import Tools.Source

import System.Environment
       
main :: IO ()
main = do
        xs <- getArgs
        case xs of
            x0:x1:_ -> do
                goto_definition x0 x1
            _ -> return ()
            