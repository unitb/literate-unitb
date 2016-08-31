{-# LANGUAGE TypeFamilies #-}
module Utilities.Functor where

import Control.Lens hiding (Traversable1(..))

import Data.Map.Class

newtype Swap1 f a b = Swap1 {swap1 :: f b a}
newtype Swap2 f a b c = Swap2 {swap2 :: f c b a}
newtype Swap3 f a b c d = Swap3 {swap3 :: f d b c a}
newtype Swap4 f a b c d e = Swap4 {swap4 :: f e b c d a}
newtype Swap5 f a b c d e g = Swap5 {swap5 :: f g b c d e a}

instance Wrapped (Swap1 f a b) where
    type Unwrapped (Swap1 f a b) = f a b
instance Wrapped (Swap2 f a b c) where
    type Unwrapped (Swap2 f a b c) = f a b c
instance Wrapped (Swap3 f a b c d) where
    type Unwrapped (Swap3 f a b c d) = f a b c d
instance Wrapped (Swap4 f a b c d e) where
    type Unwrapped (Swap4 f a b c d e) = f a b c d e
instance Wrapped (Swap5 f a b c d e g) where
    type Unwrapped (Swap5 f a b c d e g) = f a b c d e g

class Functor1 f where
    fmap1 :: (a -> b) -> f a c -> f b c
    default fmap1 :: (Traversable1 f)
                  => (a0 -> a1)
                  -> f a0 b -> f a1 b
    fmap1 f = runIdentity . traverse1 (Identity . f)

class Functor2 f where
    fmap2 :: (a -> b) -> f a c d -> f b c d
    default fmap2 :: (Traversable2 f)
                  => (a0 -> a1)
                  -> f a0 b c -> f a1 b c 
    fmap2 f = runIdentity . traverse2 (Identity . f)
    fmapOn2 :: (a -> a') 
            -> (b -> b') 
            -> (c -> c') 
            -> f a b c -> f a' b' c'
    default fmapOn2 :: (Traversable2 f)
                    => (a -> a') 
                    -> (b -> b') 
                    -> (c -> c') 
                    -> f a b c -> f a' b' c'
    fmapOn2 f g h = runIdentity . traverseOn2 
                        (Identity . f)
                        (Identity . g)
                        (Identity . h)

class Functor3 f where
    fmap3 :: (a -> b) -> f a c d e -> f b c d e
    default fmap3 :: (Traversable3 f)
                  => (a0 -> a1)
                  -> f a0 b c d -> f a1 b c d
    fmap3 f = runIdentity . traverse3 (Identity . f)

class Functor4 f where
    fmap4 :: (a -> b) -> f a c d e g -> f b c d e g
    default fmap4 :: (Traversable4 f)
                  => (a0 -> a1)
                  -> f a0 b c d e -> f a1 b c d e
    fmap4 f = runIdentity . traverse4 (Identity . f)

class Functor5 f where
    fmap5 :: (a -> b) -> f a c d e g h -> f b c d e g h
    default fmap5 :: (Traversable5 f)
                  => (a0 -> a1)
                  -> f a0 b c d e g -> f a1 b c d e g
    fmap5 f = runIdentity . traverse5 (Identity . f)

instance Functor1 f => Functor (Swap1 f a) where
    fmap f = Swap1 . fmap1 f . swap1
instance Functor2 f => Functor (Swap2 f a b) where
    fmap f = Swap2 . fmap2 f . swap2
instance Functor3 f => Functor (Swap3 f a b c) where
    fmap f = Swap3 . fmap3 f . swap3
instance Functor4 f => Functor (Swap4 f a b c d) where
    fmap f = Swap4 . fmap4 f . swap4
instance Functor5 f => Functor (Swap5 f a b c d e) where
    fmap f = Swap5 . fmap5 f . swap5

class Foldable1 f where
    foldMap1 :: Monoid m => (a -> m) -> f a b -> m
    default foldMap1 :: (Traversable1 f, Monoid m)
                     => (a -> m) -> f a b -> m
    foldMap1 f = getConst . traverse1 (Const . f)

class Foldable2 f where
    foldMap2 :: Monoid m => (a -> m) -> f a b c -> m
    default foldMap2 :: (Traversable2 f, Monoid m)
                     => (a -> m) -> f a b c -> m
    foldMap2 f = getConst . traverse2 (Const . f)

class Foldable3 f where
    foldMap3 :: Monoid m => (a -> m) -> f a b c d -> m
    default foldMap3 :: (Traversable3 f, Monoid m)
                     => (a -> m) -> f a b c d -> m
    foldMap3 f = getConst . traverse3 (Const . f)

class Foldable4 f where
    foldMap4 :: Monoid m => (a -> m) -> f a b c d e -> m
    default foldMap4 :: (Traversable4 f, Monoid m)
                     => (a -> m) -> f a b c d e -> m
    foldMap4 f = getConst . traverse4 (Const . f)

class Foldable5 f where
    foldMap5 :: Monoid m => (a -> m) -> f a b c d e g -> m
    default foldMap5 :: (Traversable5 f, Monoid m)
                     => (a -> m) -> f a b c d e g -> m
    foldMap5 f = getConst . traverse5 (Const . f)

instance Foldable1 f => Foldable (Swap1 f a) where
    foldMap f = foldMap1 f . swap1
instance Foldable2 f => Foldable (Swap2 f a b) where
    foldMap f = foldMap2 f . swap2
instance Foldable3 f => Foldable (Swap3 f a b c) where
    foldMap f = foldMap3 f . swap3
instance Foldable4 f => Foldable (Swap4 f a b c d) where
    foldMap f = foldMap4 f . swap4
instance Foldable5 f => Foldable (Swap5 f a b c d e) where
    foldMap f = foldMap5 f . swap5

class (Functor1 t,Foldable1 t) => Traversable1 t where
    traverse1 :: Applicative f 
              => (a0 -> f a1)
              -> t a0 b -> f (t a1 b)
    traverse1 f = traverseOn1 f pure
    traverseOn1 :: Applicative f 
                => (a -> f a') 
                -> (b -> f b') 
                -> t a b -> f (t a' b')
    default traverseOn1 :: (t ~ t' z,Traversable2 t',Applicative f)
                => (a -> f a') 
                -> (b -> f b') 
                -> t' z a b -> f (t' z a' b')
    traverseOn1 = traverseOn2 pure

class (Functor2 t,Foldable2 t) => Traversable2 t where
    traverse2 :: Applicative f 
              => (a0 -> f a1)
              -> t a0 b c -> f (t a1 b c)
    traverse2 f = traverseOn2 f pure pure
    traverseOn2 :: Applicative f 
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> t a b c -> f (t a' b' c')
    default traverseOn2 :: (t ~ t' z,Traversable3 t',Applicative f)
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> t' z a b c -> f (t' z a' b' c')
    traverseOn2 = traverseOn3 pure
    -- default traverseOn2 :: (Traversable2 f)
    --                 => (a -> a') 
    --                 -> (b -> b') 
    --                 -> (c -> c') 
    --                 -> f a b c -> f a' b' c'
    -- traverseOn2 f g h = runIdentity . traverseOn2 
    --                     (Identity . f)
    --                     (Identity . g)
    --                     (Identity . h)

class (Functor3 t,Foldable3 t) => Traversable3 t where
    traverse3 :: Applicative f 
              => (a0 -> f a1)
              -> t a0 b c d -> f (t a1 b c d)
    traverse3 f = traverseOn3 f pure pure pure
    traverseOn3 :: Applicative f 
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> (d -> f d') 
                -> t a b c d -> f (t a' b' c' d')
    default traverseOn3 :: (t ~ t' z,Traversable4 t',Applicative f)
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> (d -> f d') 
                -> t' z a b c d -> f (t' z a' b' c' d')
    traverseOn3 = traverseOn4 pure

class (Functor4 t,Foldable4 t) => Traversable4 t where
    traverse4 :: Applicative f 
              => (a0 -> f a1)
              -> t a0 b c d e -> f (t a1 b c d e)
    traverse4 f = traverseOn4 f pure pure pure pure
    traverseOn4 :: Applicative f 
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> (d -> f d') 
                -> (e -> f e') 
                -> t a b c d e -> f (t a' b' c' d' e')
    default traverseOn4 :: (t ~ t' z,Traversable5 t',Applicative f)
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> (d -> f d') 
                -> (e -> f e') 
                -> t' z a b c d e -> f (t' z a' b' c' d' e')
    traverseOn4 = traverseOn5 pure

class (Functor5 t,Foldable5 t) => Traversable5 t where
    traverse5 :: Applicative f 
              => (a0 -> f a1)
              -> t a0 b c d e g -> f (t a1 b c d e g)
    traverse5 f = traverseOn5 f pure pure pure pure pure
    traverseOn5 :: Applicative f 
                => (a -> f a') 
                -> (b -> f b') 
                -> (c -> f c') 
                -> (d -> f d') 
                -> (e -> f e') 
                -> (x -> f x') 
                -> t a b c d e x -> f (t a' b' c' d' e' x')

instance Traversable1 f => Traversable (Swap1 f a) where
    traverse f = fmap Swap1 . traverse1 f . swap1
instance Traversable2 f => Traversable (Swap2 f a b) where
    traverse f = fmap Swap2 . traverse2 f . swap2
instance Traversable3 f => Traversable (Swap3 f a b c) where
    traverse f = fmap Swap3 . traverse3 f . swap3
instance Traversable4 f => Traversable (Swap4 f a b c d) where
    traverse f = fmap Swap4 . traverse4 f . swap4
instance Traversable5 f => Traversable (Swap5 f a b c d e) where
    traverse f = fmap Swap5 . traverse5 f . swap5

{-# INLINE traversePairs #-}
traversePairs :: (IsKey map k1,IsMap map)
              => Traversal 
        (map k0 a0) (map k1 a1)
        (k0,a0) (k1,a1)
traversePairs f = fmap fromList . traverse f . snd . toListIntl

instance Foldable1 Map where
    foldMap1 f = foldMapWithKey $ const . f
