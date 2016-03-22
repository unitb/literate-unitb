module Utilities.MapSyntax where

    -- Libraries
import Control.Monad.Writer

import Data.Map.Class as M

newtype MapSyntax k a b = MapSyntax (Writer [(k,a)] b)
    deriving (Functor,Applicative,Monad)

(##) :: k -> a -> MapSyntax k a ()
x ## y = MapSyntax (tell [(x,y)])

runMapWith :: (M.IsMap map, M.IsKey map k) 
           => (a -> a -> a) 
           -> MapSyntax k a b 
           -> map k a
runMapWith f (MapSyntax cmd) = M.fromListWith f $ execWriter cmd

runMap' :: (M.IsMap map, M.IsKey map k) 
        => MapSyntax k a b 
        -> map k a
runMap' = runMapWith const
