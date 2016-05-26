module Control.Arrow.Unfold where

import Control.Arrow hiding (loop)
import Control.Category
import Control.Monad.State
import Control.Lens

import Data.Constraint (Dict(..))
import Data.Tuple
import Data.Unfoldable

import Prelude hiding (id,(.))

class Arrow arr => ArrowUnfold arr where
    fixA :: Unfoldable t 
         => arr a (Maybe (b,a)) -> arr a (Maybe (t b))
    fixExA :: arr a (Maybe (b,a)) -> arr (Dict (Unfoldable t),a) (Maybe (t b))
    fixA a = arr (\_ -> Dict) &&& id >>> fixExA a

instance Monad m => ArrowUnfold (Kleisli m) where
    fixExA (Kleisli f) = Kleisli $ \(Dict,x) -> unfoldM f x

instance ArrowUnfold (->) where
    fixExA f (Dict,x) = unfold f x

arrOn :: Arrow arr 
      => Lens s t a b -> arr a b -> arr s t
arrOn ln a = id &&& (arr (getConst . ln Const) >>> a) >>> arr (\(s,b) -> set ln b s)

fixExA' :: (ArrowUnfold arr)
        => arr a (Maybe b) -> arr (Dict (Unfoldable t),a) (Maybe (t b))
fixExA' a = fixExA (id &&& a >>> arr (fmap swap . sequenceA))
        
fixA' :: (ArrowUnfold arr,Unfoldable t)
      => arr a (Maybe b) -> arr a (Maybe (t b))
fixA' a = fixA (id &&& a >>> arr (fmap swap . sequenceA))

kleisli :: Iso (Kleisli m a b) (Kleisli m' c d) (a -> m b) (c -> m' d)
kleisli = iso runKleisli Kleisli

kleisli' :: Iso (a -> m b) (c -> m' d) (Kleisli m a b) (Kleisli m' c d)
kleisli' = from kleisli
