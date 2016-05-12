{-# LANGUAGE TypeFamilies #-}
module Control.CoApplicative where

import Control.Lens

import Data.Tuple

class Functor f => CoApplicative f where
    pure' :: f a -> a
    extract :: f ((a -> r) -> (b -> r) -> r) -> (f a -> r) -> (f b -> r) -> r

either' :: Either a b -> (a -> r) -> (b -> r) -> r
either' f x y = either x y f

maybe' :: Maybe a -> (() -> r) -> (a -> r) -> r
maybe' f x y = maybe (x ()) y f

instance CoApplicative Identity where
    pure' = view _Wrapped'
    {-# INLINE extract #-}
    extract (Identity x) f g = x (f.Identity) (g.Identity)

instance CoApplicative ((,) a) where
    pure' = view _2
    {-# INLINE extract #-}
    extract (x,a) f g = a (f.(x,)) (g.(x,))

instance Functor ((,,) a b) where
    {-# INLINE fmap #-}
    fmap = over _3

instance CoApplicative ((,,) a b) where
    pure' = view _3
    {-# INLINE extract #-}
    extract (x,y,a) f g = a (f.(x,y,)) (g.(x,y,))

instance Functor ((,,,) a b c) where
    {-# INLINE fmap #-}
    fmap = over _4

instance CoApplicative ((,,,) a b c) where
    pure' = view _4
    {-# INLINE extract #-}
    extract (x,y,z,a) f g = a (f.(x,y,z,)) (g.(x,y,z,))

instance Functor ((,,,,) a b c d) where
    {-# INLINE fmap #-}
    fmap = over _5

instance CoApplicative ((,,,,) a b c d) where
    pure' = view _5
    {-# INLINE extract #-}
    extract (x,y,z,w,a) f g = a (f.(x,y,z,w,)) (g.(x,y,z,w,))

instance Functor ((,,,,,) a b c d e) where
    {-# INLINE fmap #-}
    fmap = over _6

instance CoApplicative ((,,,,,) a b c d e) where
    pure' = view _6
    {-# INLINE extract #-}
    extract (x,y,z,v,w,a) f g = a (f.(x,y,z,v,w,)) (g.(x,y,z,v,w,))

{-# INLINE distr #-}
distr :: (CoApplicative f,Functor f')
      => Iso (f (Either a b)) 
             (f' (Either a' b')) 
             (Either (f a) (f b))
             (Either (f' a') (f' b'))
distr = iso (\r -> extract (either' <$> r) Left Right) (either (fmap Left) (fmap Right))

distr' :: (CoApplicative f)
       => f (Maybe a) -> Maybe (f a)
distr' r = extract (maybe' <$> r) (const Nothing) Just


{-# INLINE distrLeft #-}
distrLeft :: Iso (Either a b,z)       (Either a' b',z')
                 (Either (a,z) (b,z)) (Either (a',z') (b',z'))
distrLeft = swapped . distr . bimapping swapped swapped

distrLeft' :: (Maybe a,z) -> Maybe (a,z)
distrLeft' = fmap swap . distr' . swap
