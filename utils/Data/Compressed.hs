module Data.Compressed where

import Control.Lens
import Control.Monad.State
import Control.Precondition

import Data.Array hiding ((!))
import Data.Hashable
import Data.HashMap.Strict as H hiding ((!))
import Data.List as L
import Data.Serialize (Serialize)
import Data.Tuple

import GHC.Generics (Generic)

data Compressed f a = Compressed (Array Int a) (f Int)
    deriving (Generic)

instance (Serialize a,Serialize (f Int)) => Serialize (Compressed f a) where

packaged :: (Functor f,Traversable g,Eq b,Hashable b)
         => Iso (Compressed f a) (Compressed g b) (f a) (g b)
packaged = iso (\(Compressed ar x) -> (ar !) <$> x) compress

compress :: (Traversable f,Hashable a,Eq a)
         => f a -> Compressed f a
compress x = Compressed ar x'
    where
        ar = array (0,H.size m-1) $ L.map swap $ toList m
        (x',m) = runState (traverse f x) empty
        f i = do
                m <- get
                case H.lookup i m of
                    Just j -> return j
                    Nothing -> do
                        modify $ H.insert i (H.size m)
                        return $ H.size m

