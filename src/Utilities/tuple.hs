{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module Utilities.Tuple 
    ( module Utilities.Tuple )
where

    -- Libraries
import Data.Functor.Identity
import Data.Typeable

infixr 5 :+:

data (:+:) a b = (:+:) a b

type family Tuple a :: *
type instance Tuple () = ()
type instance Tuple (a:+:()) = Identity a
type instance Tuple (a0:+:a1:+:()) = (a0,a1)
type instance Tuple (a0:+:a1:+:a2:+:()) = (a0,a1,a2)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:()) = (a0,a1,a2,a3)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:()) = (a0,a1,a2,a3,a4)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:()) = (a0,a1,a2,a3,a4,a5)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:()) = (a0,a1,a2,a3,a4,a5,a6)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:a24:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:a24:+:a25:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:a24:+:a25:+:a26:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:a24:+:a25:+:a26:+:a27:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:a24:+:a25:+:a26:+:a27:+:a28:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28)
type instance Tuple (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:a21:+:a22:+:a23:+:a24:+:a25:+:a26:+:a27:+:a28:+:a29:+:()) = (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29)

type family Length a :: *
type instance Length () = ()
type instance Length (x:+:xs) = S (Length xs)

type family Append a b :: *
type instance Append () xs = xs
type instance Append (x:+:xs) ys = x :+: Append xs ys

type family Take a b :: *
type instance Take () xs = ()
type instance Take (S n) (x:+:xs) = x :+: Take n xs
type instance Take n () = ()

type Cons a b = Tuple (a :+: TypeList b)

type family Drop a b :: *
type instance Drop () xs = xs
type instance Drop (S n) (x:+:xs) = Drop n xs
type instance Drop n () = ()

type family TMap (f :: * -> *) xs :: *
type instance TMap f () = ()
type instance TMap f (x :+: xs) = f x :+: TMap f xs

type MapT f t = Tuple (TMap f (TypeList t))

type family TFoldL (f :: * -> * -> *) x xs :: *
type instance TFoldL f x (y :+: ys) = f x (TFoldL f y ys)
type instance TFoldL f x () = x

type family TFoldR (f :: * -> * -> *) x xs :: *
type instance TFoldR f x (y :+: ys) = TFoldR f (f x y) ys
type instance TFoldR f x () = x

type family Reverse xs :: *
type instance Reverse () = ()
type instance Reverse (x :+: xs) = Append (Reverse xs) (x :+: ())

type Id a = a

data S a = S a
    deriving Typeable



class Number a where
    value :: a -> Int

instance Number () where
    value () = 0

instance Number x => Number (S x) where
    value (S x) = 1 + value x

class IsTuple a where
    type TypeList a :: *
    toTuple :: a -> TypeList a
    fromTuple :: TypeList a -> a
    tLength :: Proxy a -> Int
    default tLength :: (IsTypeList (TypeList a)) => Proxy a -> Int
    tLength Proxy = len (Proxy :: Proxy (TypeList a))
    tMap :: (forall a. a -> f a)
         -> a -> MapT f a
    default tMap :: (a ~ Tuple (TypeList a)
                    , TypeList (Tuple (TMap f (TypeList a)))
                      ~ TMap f (TypeList a)
                    , IsTuple (Tuple (TMap f (TypeList a)))
                    , IsTypeList (TypeList a))
                 => (forall a. a -> f a)
                 -> a -> MapT f a
    tMap f x = fromTuple $ tmap f $ toTuple x

instance IsTuple () where
    type TypeList () = ()
    toTuple () = ()
    fromTuple () = ()

instance IsTuple (Identity a) where
    type TypeList (Identity a) = a :+: ()
    toTuple (Identity x) = x :+: ()
    fromTuple (x :+: ()) = Identity x 

instance IsTuple (a,b) where
    type TypeList (a,b) = (a :+: b :+: ())
    toTuple (x,y) = x :+: y :+: ()
    fromTuple (x :+: y :+: ()) = (x,y) 

instance IsTuple (a0,a1,a2) where
    type TypeList (a0,a1,a2) = (a0:+:a1:+:a2:+:())
    toTuple (x0,x1,x2) = (x0:+:x1:+:x2:+:())
    fromTuple (x0:+:x1:+:x2:+:())= (x0,x1,x2) 

instance IsTuple (a0,a1,a2,a3) where
    type TypeList (a0,a1,a2,a3) = (a0:+:a1:+:a2:+:a3:+:())
    toTuple (x0,x1,x2,x3) = (x0:+:x1:+:x2:+:x3:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:())= (x0,x1,x2,x3) 

instance IsTuple (a0,a1,a2,a3,a4) where
    type TypeList (a0,a1,a2,a3,a4) = (a0:+:a1:+:a2:+:a3:+:a4:+:())
    toTuple (x0,x1,x2,x3,x4) = (x0:+:x1:+:x2:+:x3:+:x4:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:())= (x0,x1,x2,x3,x4) 

instance IsTuple (a0,a1,a2,a3,a4,a5) where
    type TypeList (a0,a1,a2,a3,a4,a5) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:())
    toTuple (x0,x1,x2,x3,x4,a5) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:())= (x0,x1,x2,x3,x4,a5) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:())= (x0,x1,x2,x3,x4,a5,a6) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:())= (x0,x1,x2,x3,x4,a5,a6,a7) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19) 

instance IsTuple (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20) where
    type TypeList (a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20) = (a0:+:a1:+:a2:+:a3:+:a4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:())
    toTuple (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20) = (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:())
    fromTuple (x0:+:x1:+:x2:+:x3:+:x4:+:a5:+:a6:+:a7:+:a8:+:a9:+:a10:+:a11:+:a12:+:a13:+:a14:+:a15:+:a16:+:a17:+:a18:+:a19:+:a20:+:())= (x0,x1,x2,x3,x4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20) 

cons :: (IsTuple a1, IsTuple a, TypeList a ~ (x :+: TypeList a1)) =>
              x -> a1 -> a
cons x xs = fromTuple (x :+: toTuple xs)

class IsTypeList a where
    size :: Proxy a -> Length a
    len  :: Proxy a -> Int
    append :: IsTypeList b => a -> b -> Append a b
    tmap :: (forall b. b -> f b) -> a -> TMap f a
    tfoldl :: (forall b c. b -> c -> f b c) -> k -> a -> TFoldL f k a
    tfoldr :: (forall b c. b -> c -> f b c) -> k -> a -> TFoldR f k a

instance IsTypeList () where
    size _ = ()
    len _  = 0
    append _ x = x
    tmap _ _ = ()
    tfoldl _ x _ = x
    tfoldr _ x _ = x

instance IsTypeList xs => IsTypeList (x :+: xs) where
    size _ = S $ size (Proxy :: Proxy xs)
    len (_) = 1 + len (Proxy :: Proxy xs)
    append (x :+: xs) ys = x :+: append xs ys
    tmap f (x :+: xs) = f x :+: tmap f xs
    tfoldl f x (y :+: ys) = f x (tfoldl f y ys)
    tfoldr f x (y :+: ys) = tfoldr f (f x y) ys
