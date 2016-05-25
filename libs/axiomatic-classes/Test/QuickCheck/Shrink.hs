module Test.QuickCheck.Shrink where

import Control.Lens
import Control.Monad.Loops

import Test.QuickCheck
import Test.QuickCheck.Lens

doShrink :: Arbitrary a => (a -> Property) -> a -> IO a
doShrink prop x = do
        let args = stdArgs { chatty = False }
        y <- firstM (fmap (isn't _Success) . quickCheckWithResult args . prop) (shrink x)
        maybe (return x) (doShrink prop) y
