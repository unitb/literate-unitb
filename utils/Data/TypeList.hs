{-# LANGUAGE DataKinds, TypeOperators, KindSignatures
    , GADTs, TypeFamilies, ScopedTypeVariables
    , PatternSynonyms, ConstraintKinds #-}
module Data.TypeList where

import Control.Lens hiding (curried,uncurried)
import Control.Monad
import Control.Precondition

import Data.Proxy
import Data.Proxy.TH

import Language.Haskell.TH

import Utilities.TH

data List' f :: [*] -> * where 
    Cons' :: f a -> List' f as -> List' f (a ': as)
    Null  :: List' f '[]

type List = List' Identity

replicateL' :: AsTypeList t f 
            => (forall a. f a) 
            -> t
replicateL' f = replicateL f^.from asTypeList

replicateL :: forall f a. IsTypeList a => (forall a. f a) -> List' f a
replicateL x = byCase
    Null 
    (Cons' x $ replicateL x) 
    [pr|a|]
    

zipWithL :: forall f g h a m. Applicative m
         => (forall a. f a -> g a -> m (h a))
         -> List' f a -> List' g a -> m (List' h a)
zipWithL f (Cons' x xs) = (\(Cons' y ys) -> Cons' <$> (f x y) <*> zipWithL f xs ys) 
        :: (a ~ (x ': xs)) => List' g (x ': xs) -> m (List' h (x ': xs))
zipWithL _ Null = (\Null -> pure Null) :: List' g '[] -> m (List' h '[])

zipWithL' :: forall f g h a. 
             (forall a. f a -> g a -> h a)
          -> List' f a -> List' g a -> List' h a
zipWithL' f xs ys = runIdentity $ zipWithL (f & mapped.mapped %~ Identity) xs ys

data Pair f g a = Pair (f a) (g a)

zipL :: List' f a -> List' g a -> List' (Pair f g) a
zipL = zipWithL' Pair

class IsTypeList (TypeListOf t) => IsTuple t where
    type TypeListOf t :: [*]
    type ReplaceF (f :: * -> *) t :: *

class (IsTuple a, ReplaceF f a ~ a) => AsTypeList a f where
    -- type FunTypeOf a f r :: *
    asTypeList' :: Iso' a (List' f (TypeListOf a))

class Curried t r f | t r -> f, f r -> t, f t -> r where
    curried' :: Iso' (t -> r) f

curried :: (Curried t r f, Curried t' r' f')
        => Iso (t -> r) (t' -> r') f f'
curried = withIso curried' $ \f _ -> withIso curried' $ \_ f' -> iso f f'

uncurried :: (Curried t r f, Curried t' r' f')
          => Iso f f' (t -> r) (t' -> r')
uncurried = from curried

uncurried' :: Curried t r f => Iso' f (t -> r)
uncurried' = from curried'

{-# INLINE asTypeList #-}
asTypeList :: (AsTypeList a f,AsTypeList b g)
           => Iso a b (List' f (TypeListOf a)) (List' g (TypeListOf b))
asTypeList = withIso asTypeList' $ \ sa _ -> withIso asTypeList' $ \ _ bt -> iso sa bt

type family TupleOf xs (f :: * -> *) :: * where
    TupleOf '[] f = ()
    TupleOf '[a] f = Identity (f a)
    TupleOf '[a0,a1] f = (f a0,f a1)

class IsTypeList xs where
    byCase :: ((xs ~ '[]) => r) 
           -> (forall a as. (IsTypeList as,xs ~ (a ': as)) => r)
           -> Proxy xs
           -> r

byCase' :: forall f xs r. (IsTypeList xs)
        => ((xs ~ '[]) => () -> r) 
        -> (forall a as. (IsTypeList as,xs ~ (a ': as)) 
                => f a 
                -> List' f as -> r)
        -> List' f xs
        -> r
byCase' f g xs = byCase (\Null -> f ()) ((\(Cons' x xs) -> g x xs)) [pr|xs|] xs

instance IsTypeList '[] where
    byCase f _ Proxy = f

instance IsTypeList xs => IsTypeList (x ': xs) where
    byCase _ f Proxy = f

type SameLength a b = (IsTuple a,IsTuple b,TypeListOf a ~ TypeListOf b)

traverseL :: Applicative m 
          => (forall a. f a -> m (g a)) 
          -> List' f a -> m (List' g a) 
traverseL _ Null = pure Null
traverseL f (Cons' x xs) = Cons' <$> f x <*> traverseL f xs

mapL :: (forall a. f a -> g a)
     -> List' f a -> List' g a
mapL f = runIdentity . traverseL (Identity . f)

tailL :: List' f (a ': as) -> List' f as
tailL (Cons' _ xs) = xs

headL :: List' f (a ': as) -> f a
headL (Cons' x _) = x

do
    let n = 20
        f = varT $ mkName "f"
        g = varT $ mkName "g"
        r = varT $ mkName "r"
        tupT 1 = [t|Identity|]
        tupT n = tupleT n
        tupleP [x] = [p|Identity $x|]
        tupleP xs  = tupP xs
        tupleE [x] = [e|Identity $x|]
        tupleE xs  = tupE xs
        typeListE :: [ExpQ] -> ExpQ
        typeListE [] = [e|Null|]
        typeListE (x:xs) = appE [e|Cons' $x|] (typeListE xs)
        typeListP [] = [p|Null|]
        typeListP (x:xs) = [p| Cons' $x $(typeListP xs) |]
        args = [ mkName $ 'a' : show i | i <- [0..] ]
        list [] = promotedNilT
        list (t:ts) = appsT [promotedConsT,t,list ts]
    fmap concat $ forM [0..n] $ \i -> do
        let t = appsT $ tupT i : fargs
            t' = appsT $ tupT i : gargs
            fargs = map (appT f) argT
            gargs = map (appT g) argT
            ffP = varP $ mkName "f"
            ffE = varE $ mkName "f"
            tList = list argT
            argT  = varT <$> take i args
            argE  = varE <$> take i args
            argP  = varP <$> take i args
            toFun = lam1E (tupleP argP) (typeListE argE)
            fromFun = lamCaseE $
                        [ match (typeListP argP) (normalB $ tupleE argE) [] ]
                        ++ (guard (i > 0) >> [ match wildP (normalB [e|undefined'|]) [] ])
            curry' = lamE (ffP:argP) (appE ffE $ tupleE argE)
            uncurry' = lamE [ffP,tupleP argP] (appsE $ ffE : argE)
        [d| instance AsTypeList $t $f where
                {-# INLINE asTypeList' #-}
                asTypeList' = iso $toFun $fromFun 
            instance IsTuple $t where
                type TypeListOf $t = $tList
                type ReplaceF $g $t = $t'
            instance Curried $(appsT $ tupT i : argT) $r $(arrowType' argT r) where
                {-# INLINE curried' #-}
                curried' = iso $curry' $uncurry' |]
