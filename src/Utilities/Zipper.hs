{-# LANGUAGE TypeFamilies
    , GADTs
    , EmptyCase
    , TypeOperators
    , EmptyDataDecls
    , ScopedTypeVariables
    , UndecidableInstances
    , ExistentialQuantification
    #-}
module Utilities.Zipper where

import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Arrow hiding (right)
import Control.Lens  hiding (from,to,children,elements)

import Data.Char
import Data.Functor.Compose
import Data.Maybe
--import Data.Monoid
import Data.Proxy
import Data.Traversable
import Data.Typeable

import Prelude hiding (sequence)

import GHC.Generics

import Text.Printf
import Test.QuickCheck

data Tree a = Node a (Tree a) (Tree a) | Leaf | Many [Tree a]
    deriving (Generic,Show,Typeable)

data MTree1 a = Leaf1 a | Node1 (MTree2 a) (MTree2 a)
    deriving (Generic,Show,Typeable)

data MTree2 a = Leaf2 | Node2 [MTree1 a]
    deriving (Generic,Show,Typeable)

-- Zippers on LaTeX parse trees for mutation testing

class GZippable a b where
    data GZipper a b :: *
    data GWhole a b :: *
    gZipperEq :: GZipper a b -> GZipper a b -> Bool 
    gWholeEq :: GWhole a b -> GWhole a b -> Bool 
    gWhole :: a p -> GWhole a b
    gGet   :: GWhole a b -> a p
    gTraverseZ :: Applicative f => (b -> f b) 
               -> GZipper a b -> f (GZipper a b)
    gTraverseW :: Applicative f => (b -> f b) 
               -> GWhole a b -> f (GWhole a b)
    gRoot :: a p -> Maybe (b, GZipper a b)
    gNext :: b -> GZipper a b -> Maybe (b, GZipper a b)
    gPrev :: b -> GZipper a b -> Maybe (b, GZipper a b)
    gFill :: b -> GZipper a b -> a p
    gShow :: GZipper a b -> String
    gShowStuff :: a p -> Proxy b -> String

newtype ZipperT a = ZipperT (GZipper (Rep a) a)

newtype Zipper a = Zipper (ZipperImpl a)

class IsZipper b a | b -> a where
    zipperEqAux :: Eq a => b -> b -> Bool
    rootAux :: a -> Maybe (a,b)
    nextAux :: a -> b -> Maybe (a,b)
    prevAux :: a -> b -> Maybe (a,b)
    fillAux :: a -> b -> a
    showAux :: b -> String
    traverseZipperAux :: Applicative f => (a -> f a) -> b -> f b

class Zippable a where
    type ZipperImpl a :: *
    type ZipperImpl a = ZipperT a
    zipperEq :: Eq a => Zipper a -> Zipper a -> Bool
    root :: a -> Maybe (a,Zipper a)
    next :: a -> Zipper a -> Maybe (a,Zipper a)
    prev :: a -> Zipper a -> Maybe (a,Zipper a)
    fill :: a -> Zipper a -> a
    traverseZipper :: Applicative f => (a -> f a) -> Zipper a -> f (Zipper a)
    zshow :: Zipper a -> String
    default zipperEq :: (IsZipper (ZipperImpl a) (Identity a), Eq a)
                     => Zipper a -> Zipper a -> Bool 
    zipperEq (Zipper x) (Zipper y) = zipperEqAux x y
    default root :: (IsZipper (ZipperImpl a) (Identity a))
                 => a -> Maybe (a,Zipper a)
    root = fmap (runIdentity *** Zipper) . rootAux . Identity
    default traverseZipper :: ( IsZipper (ZipperImpl a) (Identity a)
                              , Applicative f) 
                 => (a -> f a) 
                 -> Zipper a 
                 -> f (Zipper a)
    traverseZipper f (Zipper x) = Zipper <$> traverseZipperAux (fmap Identity . f . runIdentity) x
    --default root :: (Generic a, GZippable (Rep a) a) 
    --             => a -> Maybe (a,Zipper a)
    default fill :: (IsZipper (ZipperImpl a) (Identity a)) 
                 => a -> Zipper a -> a
    fill x (Zipper z) = runIdentity $ fillAux (Identity x) z
    default next :: (IsZipper (ZipperImpl a) (Identity a)) 
                 => a -> Zipper a -> Maybe (a,Zipper a)
    next x (Zipper z) = (runIdentity *** Zipper) <$> nextAux (Identity x) z
    default prev :: (IsZipper (ZipperImpl a) (Identity a)) 
                 => a -> Zipper a -> Maybe (a,Zipper a)
    prev x (Zipper z) = (runIdentity *** Zipper) <$> prevAux (Identity x) z
    default zshow :: (IsZipper (ZipperImpl a) (Identity a)) 
                  => Zipper a -> String
    zshow (Zipper x) = showAux x

instance (Generic a, GZippable (Rep a) a) => IsZipper (ZipperT a) (Identity a) where
    zipperEqAux (ZipperT x) (ZipperT y) = gZipperEq x y
    rootAux = fmap (Identity *** ZipperT) . gRoot . from . runIdentity
    nextAux (Identity x) (ZipperT z) = (Identity *** ZipperT) <$> gNext x z
    prevAux (Identity x) (ZipperT z) = (Identity *** ZipperT) <$> gPrev x z
    fillAux (Identity x) (ZipperT z) = Identity $ to $ gFill x z
    showAux (ZipperT x) = gShow x
    traverseZipperAux f (ZipperT x) = ZipperT <$> gTraverseZ (fmap runIdentity . f . Identity) x

instance (Eq a, Zippable a) => Eq (Zipper a) where
    (==) = zipperEq

instance GZippable (Rep a) a => Eq (ZipperT a) where
    ZipperT x == ZipperT y = gZipperEq x y

instance (GZippable (Rep a) b,GZippable (Rep b) a) => Eq (MZipperT a b) where
    MZipperT x0 x1 == MZipperT y0 y1 = gZipperEq x0 y0 && gZipperEq x1 y1

gZippers :: GZippable a b => a p -> [(b,GZipper a b)] 
gZippers x = maybe [] (uncurry gSiblings) $ gRoot x

gSiblings :: GZippable a b => b -> GZipper a b -> [(b,GZipper a b)] 
gSiblings x y = (x,y) : maybe [] (uncurry gSiblings) (gNext x y)

gBefore :: GZippable a b => b -> GZipper a b -> [(b,GZipper a b)] 
gBefore x y = (x,y) : maybe [] (uncurry gBefore) (gPrev x y)

gLast :: GZippable a b => a p -> Maybe (b,GZipper a b)
gLast x = listToMaybe $ reverse $ gZippers x

data MZipperT a b = MZipperT (GZipper (Rep a) b) (GZipper (Rep b) a)

instance (Generic a, Generic b, GZippable (Rep a) b, GZippable (Rep b) a) 
        => IsZipper (MZipperT a b) (Identity a) where
    zipperEqAux (MZipperT zA0 zB0) (MZipperT zA1 zB1) = gZipperEq zA0 zA1 && gZipperEq zB0 zB1
    rootAux (Identity x) = first Identity <$> (z0 >>= z1)
        where
            z0 = gRoot (from x)
            z1 (r,z') = second (MZipperT z') <$> gRoot (from r)
    nextAux (Identity x) (MZipperT z0 z1) = ((Identity *** MZipperT z0) <$> gNext x z1) <|> other
        where 
            other :: Maybe (Identity a,MZipperT a b)
            other = listToMaybe $ mapMaybe (f) $ drop 1 xs
            f (x,z) = (Identity *** MZipperT z) <$> gRoot (from x)
            xs :: [(b,GZipper (Rep a) b)]
            xs = gSiblings (to $ gFill x z1) z0
    prevAux (Identity x) (MZipperT z0 z1) = ((Identity *** MZipperT z0) <$> gPrev x z1) <|> other
        where 
            other :: Maybe (Identity a,MZipperT a b)
            other = listToMaybe $ mapMaybe (f) $ drop 1 xs
            f (x,z) = (Identity *** MZipperT z) <$> gLast (from x)
            xs :: [(b,GZipper (Rep a) b)]
            xs = gBefore (to $ gFill x z1) z0
    fillAux (Identity x) (MZipperT z0 z1) = Identity $ to $ gFill (to $ gFill x z1) z0
    showAux (MZipperT z0 z1) = printf "( %s,%s )" (gShow z0) (gShow z1)
    traverseZipperAux f (MZipperT z0 z1) = 
                MZipperT <$> gTraverseZ (fmap to'.gTraverseW f'.from') z0 
                         <*> gTraverseZ f' z1
        where
            f' = fmap runIdentity.f.Identity
            to' = to.gGet
            from' = gWhole.from

instance (Zippable a) => Show (Zipper a) where
    show = zshow

instance (Show a,Typeable a) => Zippable (Tree a) where
    --type ZipperImpl (Tree a) = ZipperT (Tree a)

instance (Show a,Typeable a) => 
        Zippable (MTree1 a) where
    type ZipperImpl (MTree1 a) = MZipperT (MTree1 a) (MTree2 a)

instance GZippable a t => GZippable (D1 d a) t where
    newtype GZipper (D1 d a) t = D1Zipper (GZipper a t)
    newtype GWhole (D1 d a) t = D1Whole (GWhole a t)
    gZipperEq (D1Zipper x) (D1Zipper y) = gZipperEq x y
    gWholeEq (D1Whole x) (D1Whole y) = gWholeEq x y
    gTraverseZ f (D1Zipper x) = D1Zipper <$> gTraverseZ f x
    gTraverseW f (D1Whole x) = D1Whole <$> gTraverseW f x
    gWhole = D1Whole . gWhole . unM1
    gGet (D1Whole x) = M1 $ gGet x
    gRoot (M1 x) = second D1Zipper <$> gRoot x
    gNext x (D1Zipper z) = second D1Zipper <$> gNext x z
    gPrev x (D1Zipper z) = second D1Zipper <$> gPrev x z
    gFill x (D1Zipper z) = M1 $ gFill x z
    gShow (D1Zipper x) = gShow x
    gShowStuff (M1 x)  = gShowStuff x

data Hole a b where
    Hole :: Hole a a
    ListHole :: [a] -> [a] -> Hole [a] a

instance (Show a,Show t,Typeable t,Eq t,Typeable a) => GZippable (K1 k a) t where
    newtype GZipper (K1 k a) t = K1Zipper (Hole a t)
    newtype GWhole (K1 k a) t = K1Whole a
    gZipperEq (K1Zipper Hole) (K1Zipper Hole) = True
    gZipperEq (K1Zipper (ListHole xs0 ys0)) (K1Zipper (ListHole xs1 ys1)) = xs0 == xs1 && ys0 == ys1
    gWhole = K1Whole . unK1
    gGet (K1Whole x) = K1 x
    gTraverseZ _ (K1Zipper Hole) = pure $ K1Zipper Hole
    gTraverseZ f (K1Zipper (ListHole xs ys)) = fmap K1Zipper $
            ListHole
                <$> traverse f xs 
                <*> traverse f ys
    gTraverseW f (K1Whole a) = K1Whole <$> 
            case eqT :: Maybe (a :~: t) of
                Just Refl -> f a
                Nothing -> case eqT :: Maybe (a :~: [t]) of
                        Just Refl -> traverse f a
                        Nothing -> pure a

    gRoot (K1 x) = case eqT :: Maybe (a :~: t) of
                Just Refl -> Just (x,K1Zipper Hole)
                Nothing -> case eqT :: Maybe (a :~: [t]) of
                        Just Refl -> case x of
                                y:ys -> Just (y,K1Zipper $ ListHole [] ys)
                                []   -> Nothing
                        Nothing   -> Nothing
    gNext _ (K1Zipper Hole) = Nothing
    gNext x (K1Zipper (ListHole xs (x':xs'))) = Just (x',K1Zipper $ ListHole (x:xs) xs')
    gNext _ (K1Zipper (ListHole _ [])) = Nothing
    gPrev _ (K1Zipper Hole) = Nothing
    gPrev x (K1Zipper (ListHole (x':xs') xs)) = Just (x',K1Zipper $ ListHole xs' (x:xs))
    gPrev _ (K1Zipper (ListHole [] _)) = Nothing
    gFill x (K1Zipper Hole) = K1 x
    gFill x (K1Zipper (ListHole xs ys)) = K1 $ reverse xs ++ [x] ++ ys
    gShow (K1Zipper Hole) = "_"
    gShow (K1Zipper (ListHole xs ys)) = show $ map sshow (reverse xs) ++ [ShowString "_"] ++ map sshow ys
    gShowStuff (K1 x) Proxy 
            | any isSpace c = printf "(%s)" c
            | otherwise     = c
        where
            c = show x

newtype ShowString = ShowString String

sshow :: Show a => a -> ShowString
sshow = ShowString . show

instance Show ShowString where
    show (ShowString x) = x

--instance (Show a) => GZippable (K1 k a) a where
--    data GZipper (K1 k a) a = K1Hole
--    gRoot (K1 x) = Just (K1Hole,x)
--    gShow (K1Hole x) = "_"
--    gShowStuff (K1 x)  = show x

instance (GZippable a t,Constructor c) => GZippable (C1 c a) t where
    newtype GZipper (C1 c a) t = C1Zipper (GZipper a t)
    newtype GWhole (C1 c a) t = C1Whole (GWhole a t)
    gZipperEq (C1Zipper x) (C1Zipper y) = gZipperEq x y
    gWholeEq (C1Whole x) (C1Whole y) = gWholeEq x y
    gWhole = C1Whole . gWhole . unM1
    gGet (C1Whole x) = M1 $ gGet x
    gTraverseZ f (C1Zipper x) = C1Zipper <$> gTraverseZ f x
    gTraverseW f (C1Whole x) = C1Whole <$> gTraverseW f x
    gRoot (M1 x) = second C1Zipper <$> gRoot x
    gNext x (C1Zipper z) = second C1Zipper <$> gNext x z
    gPrev x (C1Zipper z) = second C1Zipper <$> gPrev x z
    gFill x (C1Zipper z) = M1 $ gFill x z
    gShow (C1Zipper z) = printf "%s %s" (conName cnt) $ gShow z
        where
            cnt = undefined :: C1 c a p
    gShowStuff c@(M1 x) p = printf "%s %s" (conName c) $ gShowStuff x p

instance (GZippable a t, Selector s) => GZippable (S1 s a) t where
    newtype GZipper (S1 s a) t = S1Zipper (GZipper a t)
    newtype GWhole (S1 s a) t = S1Whole (GWhole a t)
    gZipperEq (S1Zipper x) (S1Zipper y) = gZipperEq x y
    gWholeEq (S1Whole x) (S1Whole y) = gWholeEq x y
    gWhole = S1Whole . gWhole . unM1
    gGet (S1Whole x) = M1 $ gGet x
    gTraverseZ f (S1Zipper x) = S1Zipper <$> gTraverseZ f x
    gTraverseW f (S1Whole x) = S1Whole <$> gTraverseW f x
    gRoot (M1 x) = second S1Zipper <$> gRoot x
    gNext x (S1Zipper z) = second S1Zipper <$> gNext x z
    gPrev x (S1Zipper z) = second S1Zipper <$> gPrev x z
    gFill x (S1Zipper z) = M1 $ gFill x z
    gShow (S1Zipper z) = gShow z
    gShowStuff (M1 z) = gShowStuff z

instance GZippable U1 t where
    data GZipper U1 t
    data GWhole U1 t = U1Whole
    gZipperEq x _ = case x of
    gWholeEq U1Whole U1Whole = True
    gWhole _ = U1Whole
    gGet _ = U1
    gTraverseZ _ x = case x of
    gTraverseW _ U1Whole = pure U1Whole
    gRoot U1 = Nothing
    gNext _ x = case x of
    gPrev _ x = case x of
    gFill _ x = case x of
    gShow x = case x of
    gShowStuff _ Proxy = ""

instance (GZippable a t,GZippable b t) => GZippable (a :*: b) t where
    data GZipper (a :*: b) t = 
        LeftZip (GZipper a t) (GWhole b t)
        | RightZip (GWhole a t) (GZipper b t)
    data GWhole (a :*: b) t = TimesWhole (GWhole a t) (GWhole b t)
    gZipperEq (LeftZip x0 x1) (LeftZip y0 y1) = gZipperEq x0 y0 && gWholeEq x1 y1
    gWholeEq (TimesWhole x0 x1) (TimesWhole y0 y1) = gWholeEq x0 y0 && gWholeEq x1 y1
    gWhole (x :*: y) = TimesWhole (gWhole x) (gWhole y)
    gGet (TimesWhole x y) = gGet x :*: gGet y
    gTraverseZ f (LeftZip z w) = LeftZip <$> gTraverseZ f z 
                                         <*> gTraverseW f w
    gTraverseZ f (RightZip z w) = RightZip <$> gTraverseW f z 
                                           <*> gTraverseZ f w
    gTraverseW f (TimesWhole x y) = TimesWhole <$> gTraverseW f x 
                                               <*> gTraverseW f y
    gRoot (x :*: y) =   getCompose ((`LeftZip` gWhole y) <$> Compose (gRoot x)) 
                    <|> getCompose (RightZip (gWhole x) <$> Compose (gRoot y))
    gNext x (LeftZip z w) =    getCompose ((`LeftZip` w) <$> Compose (gNext x z))
                           <|> getCompose (RightZip (gWhole $ gFill x z) <$> Compose (gRoot $ gGet w))
    gNext x (RightZip w z) =    getCompose (RightZip w <$> Compose (gNext x z))
    gPrev x (LeftZip z w) =    getCompose ((`LeftZip` w) <$> Compose (gPrev x z))
    gPrev x (RightZip w z) =    getCompose ((RightZip w) <$> Compose (gPrev x z))
                           <|> getCompose ((`LeftZip` (gWhole $ gFill x z)) <$> Compose (gRoot $ gGet w))
    gFill x (LeftZip z w)  = (gFill x z :*: gGet w)
    gFill x (RightZip w z) = (gGet w :*: gFill x z)
    gShow (LeftZip x y)  = printf "%s %s" (gShow x) (gShowStuff (gGet y) (Proxy :: Proxy t))
    gShow (RightZip x y) = printf "%s %s" (gShowStuff (gGet x) (Proxy :: Proxy t)) (gShow y)
    gShowStuff (x :*: y) p = printf "%s %s" (gShowStuff x p) (gShowStuff y p)

instance (GZippable a t,GZippable b t) => GZippable (a :+: b) t where
    data GZipper (a :+: b) t = 
            LeftZipper (GZipper a t)
            | RightZipper (GZipper b t)
    data GWhole (a :+: b) t =
            LeftWhole (GWhole a t)
            | RightWhole (GWhole b t)
    gZipperEq (LeftZipper x) (LeftZipper y) = gZipperEq x y
    gZipperEq (RightZipper x) (RightZipper y) = gZipperEq x y
    gWholeEq (LeftWhole x) (LeftWhole y) = gWholeEq x y
    gWholeEq (RightWhole x) (RightWhole y) = gWholeEq x y
    gWhole (L1 x) = LeftWhole $ gWhole x
    gWhole (R1 x) = RightWhole $ gWhole x
    gTraverseZ f (LeftZipper x)  = LeftZipper <$> gTraverseZ f x
    gTraverseZ f (RightZipper x) = RightZipper <$> gTraverseZ f x
    gTraverseW f (LeftWhole x)   = LeftWhole <$> gTraverseW f x
    gTraverseW f (RightWhole x)  = RightWhole <$> gTraverseW f x
    gGet (LeftWhole x) = L1 $ gGet x
    gGet (RightWhole x) = R1 $ gGet x
    gRoot (L1 x) = second LeftZipper <$> gRoot x
    gRoot (R1 x) = second RightZipper <$> gRoot x
    gNext x (LeftZipper z)  = second LeftZipper <$> gNext x z
    gNext x (RightZipper z) = second RightZipper <$> gNext x z
    gPrev x (LeftZipper z)  = second LeftZipper <$> gPrev x z
    gPrev x (RightZipper z) = second RightZipper <$> gPrev x z
    gFill x (LeftZipper z) = L1 $ gFill x z
    gFill x (RightZipper z) = R1 $ gFill x z
    gShow (LeftZipper z) = gShow z
    gShow (RightZipper z) = gShow z
    gShowStuff (L1 x)     = gShowStuff x
    gShowStuff (R1 x)     = gShowStuff x

data Cursor a = Cursor a [Zipper a]
    deriving Show

cursor :: a -> Cursor a
cursor x = Cursor x []

up :: Zippable a => Cursor a -> Maybe (Cursor a)
up (Cursor _ []) = Nothing
up (Cursor x (z:zs)) = Just $ Cursor (fill x z) zs

down :: Zippable a => Cursor a -> Maybe (Cursor a)
down (Cursor x zs) = uncurry Cursor . second (:zs) <$> root x

left :: Zippable a => Cursor a -> Maybe (Cursor a)
left (Cursor _ []) = Nothing
left (Cursor x (z:zs)) = uncurry Cursor . second (:zs) <$> prev x z

right :: Zippable a => Cursor a -> Maybe (Cursor a)
right (Cursor _ []) = Nothing
right (Cursor x (z:zs)) = uncurry Cursor . second (:zs) <$> next x z

top :: Zippable a => Cursor a -> Cursor a
top c = maybe c top $ up c

bottom :: Zippable a => Cursor a -> Cursor a
bottom c = maybe c bottom $ down c

traverseCursor :: (Applicative f, Zippable a)
               => (a -> f a)
               -> Cursor a -> f (Cursor a) 
traverseCursor f (Cursor x zs) = Cursor 
                        <$> f x 
                        <*> traverse (traverseZipper f) zs

hole :: (Functor f, Zippable a)
             => (a -> f a)
             -> Cursor a -> f (Cursor a) 
hole f (Cursor x zs) = (`Cursor` zs) <$> f x

close :: Zippable a => Cursor a -> a
close c = case top c of
            Cursor x _ -> x

allNodes :: Zippable a => a -> [a]
allNodes a = map (view hole) $ allCursors a

allCursors :: Zippable a => a -> [Cursor a]
allCursors a = allCursors' c
    where
        c = cursor a

allCursors' :: Zippable a => Cursor a -> [Cursor a]
allCursors' c = c : concatMap allCursors' (children c)

children :: Zippable a => Cursor a -> [Cursor a]
children c = maybe [] siblings c'
    where
        c' = down c

zippers :: Zippable a => a -> [(a,Zipper a)]
zippers c = maybe [] f $ root c
    where
        f (x,y) = (x,y) : maybe [] f (next x y)

siblings :: Zippable a => Cursor a -> [Cursor a]
siblings c = c : maybe [] siblings (right c) 

mutate :: Zippable a => (a -> Gen a) -> a -> Gen a 
mutate f x = do
    let xs = allCursors x
    if null xs 
    then f x
    else do
        c <- elements xs
        close <$> hole f c

instance (Traversable g, Monad f, Monad g) => Monad (Compose f g) where
    return = Compose . return . return
    m >>= f = Compose $ liftM join $ join $ liftM sequence $ getCompose $ liftM (getCompose.f) m

treeDiff :: Eq a => Zippable a => a -> a -> ([Zipper a],a,a)
treeDiff x y = maybe ([],x,y) f zs
    where
        f (z,x,y) = treeDiff x y & _1 %~ (++[z])
        eq (x0,z0) (x1,z1)
            | z0 == z1  = Just (z0,x0,x1)
            | otherwise = Nothing 
        xs = zippers x
        ys = zippers y
        zs = msum $ zipWith eq xs ys

main :: IO ()
main = do
    let t = Node "a" (Node "b" Leaf Leaf) (Many [Node "c" Leaf Leaf,Node "d" Leaf Leaf,Node "e" Leaf Leaf])
    print t
    print $ root t
    print $ root t >>= uncurry next
    print $ uncurry fill <$> (root t >>= uncurry next )
    print $ cursor t
    print $ down (cursor t) >>= right
    print $ down (cursor t) >>= right >>= right
    print $ down (cursor t) >>= right >>= down
    print $ down (cursor t) >>= right >>= down >>= right
    print $ down (cursor t) >>= right >>= down >>= right >>= down
    print $ down (cursor t) >>= right >>= down >>= right >>= right
    print $ down (cursor t) >>= right >>= down >>= right >>= up
    print $ down (cursor t) >>= right >>= down >>= right >>= up >>= up

    putStrLn "Hello World"
    mapM_ print $ allCursors t
    putStrLn "Hello World"
    let t' = Node1 (Node2 [Leaf1 "a",Leaf1 "b",Leaf1 "c"]) (Node2 [Leaf1 "c",Node1 Leaf2 Leaf2,Leaf1 "e"])
    mapM_ print $ allCursors t'
    let f Leaf = return Leaf
        f (Node _ t0 t1) = Node <$> arbitrary <*> pure t0 <*> pure t1
        f (Many xs)      = Many <$> ((:) <$> (Node <$> arbitrary <*> pure Leaf <*> pure Leaf) 
                                         <*> pure xs)
    print t'
    mapM_ print =<< sample' (mutate f t)
