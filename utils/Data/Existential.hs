{-# LANGUAGE KindSignatures
    ,ConstraintKinds
    ,UndecidableInstances
    ,ExistentialQuantification
    ,ScopedTypeVariables
    ,TypeOperators
    #-}
module Data.Existential where

import Control.Applicative as A
import Control.Arrow
import Control.Category
import Control.Lens
import Control.Monad

import Data.Maybe
import Data.Typeable

import GHC.Exts (Constraint)

import Language.Haskell.TH

import Prelude hiding ((.),id)

import Test.QuickCheck

import Text.Printf

-- |
-- = The Cell Type

-- | A polymorphic cell. Type 'Cell MyClass' can take a value of any
-- type that conforms to 'MyClass' and to 'Typeable'. It is defined
-- in terms of 'Cell1'.
type Cell = Cell1 Identity

data Cell1 f (constr :: * -> Constraint) = forall a. (constr a, Typeable a) => Cell (f a)
-- ^ Generilization of 'Cell'. 'Cell1 MyFunctor MyClass' takes values
-- ^ of type 'MyFunctor a' with '(MyClass a,Typeable a)'.

type Inst constr a = Inst1 Identity constr a

data Inst1 f constr a = (Typeable a,constr a) => Inst (f a)

type EntailsAll c0 c1 = forall a. c0 a :- c1 a

data Dict p = p => D

newtype p :- q = Sub (p => Dict q)

dictFunToEntails :: Iso' (Dict p -> Dict q) (p :- q)
dictFunToEntails = from entailsToDictFun

entailsToDictFun :: Iso' (p :- q) (Dict p -> Dict q)
entailsToDictFun = iso (\(Sub x) D -> x) (\f -> Sub $ f D)

dict :: Inst1 f constr a -> Dict (constr a)
dict (Inst _) = D

instance Category (:-) where
    id  = Sub D
    x . y = view dictFunToEntails $ (x^.entailsToDictFun) . (y^.entailsToDictFun)

-- | 'HasCell' permits the overloading of "Iso" 'cell' and makes it easier
-- | to wrap a 'Cell' with a newtype without having to mention 'Cell' all
-- | the time.
class HasCell a b | a -> b where
    cell :: Iso' a b

instance HasCell (Cell1 f constr) (Cell1 f constr) where
    cell = id

-- |
-- = Contructors

makeCell :: (HasCell a (Cell constr), constr b, Typeable b)
         => b -> a
-- ^ We can use 'makeCell "hello" :: MyType' if there is an instance
-- ^ 'HasCell MyType (Cell Show)' (or any other class than show).
makeCell = makeCell1 . Identity

-- ^ Similar to 'makeCell'. Uses 'Cell1' to allow the content
-- ^ of a 'Cell' to be wrapped with a generic type.
makeCell1 :: (HasCell a (Cell1 f constr), constr b, Typeable b)
          => f b -> a
makeCell1 x = Cell x ^. from cell

-- |
-- = Prisms

_Cell :: (constr b,Typeable b,Typeable a) => Prism (Cell constr) (Cell constr) a b
-- ^ Treats a 'Cell' as an unbounded sum type: 'c^?_Cell :: Maybe a' has the
-- ^ value 'Just x' if x is of type 'a' and 'c' contains value 'x'. If cell 'c'
-- ^ has a value of any other type then 'a', 'c^?_Cell == Nothing'.
_Cell = _Cell1._Wrapped

_Cell' :: (constr a,Typeable a,HasCell c (Cell constr)) => Prism c c a a
-- ^ Similar to '_Cell' but operates on types that wrap a cell instead of
-- ^ on the cell itself.
_Cell' = cell.asCell

_Cell1 :: (constr b,Typeable b,Typeable a,Typeable f) 
       => Prism (Cell1 f constr) (Cell1 f constr) (f a) (f b)
-- ^ Similar to '_Cell' but values are wrapped in type 'f' inside the cell.
_Cell1 = prism Cell $ \x -> maybe (Left x) Right $ readCell1 cast x

_Cell1' :: (constr a,Typeable a,Typeable f,HasCell c (Cell1 f constr)) => Prism c c (f a) (f a)
-- ^ Analogous to '_Cell'' and '_Cell1'.
_Cell1' = cell.asCell1

asCell :: (constr a,Typeable a) 
       => Prism (Cell constr) (Cell constr) a a
-- ^ Like '_Cell' but disallows changing the type of the content of the cell.
-- ^ facilitates type checking when the prism is not used for modification.
asCell = _Cell

asCell1 :: (constr a,Typeable a,Typeable f) 
        => Prism (Cell1 f constr) (Cell1 f constr) (f a) (f a)
-- ^ Like '_Cell1' and as 'asCell'.
asCell1 = _Cell1

asInst  :: Functor g
        => (forall a. Inst1 f constr a -> g (Inst1 h constr' a))
        -> Cell1 f constr -> g (Cell1 h constr')
asInst  = asInst1

asInst1 :: Functor g
        => (forall a. Inst1 f constr a -> g (Inst1 h constr' a))
        -> Cell1 f constr -> g (Cell1 h constr')
asInst1 f (Cell x) = fromInst <$> f (Inst x)

fromInst :: Inst1 f constr a -> Cell1 f constr 
fromInst (Inst x) = (Cell x)

inst :: Lens' (Inst constr a) a
inst = inst1._Wrapped

inst1 :: Lens (Inst1 f constr a) (Inst1 g constr a) (f a) (g a)
inst1 = lens (\(Inst x) -> x) (\(Inst _) y -> Inst y) -- Inst

-- |
-- = Traversals

traverseCell :: Functor f => (forall a. (constr a,Typeable a) => a -> f a) 
             -> Cell constr -> f (Cell constr)
traverseCell f = traverseCell1 $ _Wrapped f

traverseCell' :: (Functor f,HasCell c (Cell constr))
              => (forall a. (constr a,Typeable a) => a -> f a) -> c -> f c
traverseCell' f = cell (traverseCell f)

traverseCell1 :: Functor f 
              => (forall a. (constr a,Typeable a) => g a -> f (h a))
              -> Cell1 g constr -> f (Cell1 h constr)
traverseCell1 f (Cell x) = Cell <$> f x

traverseCell1' :: (Functor f,HasCell c (Cell1 g constr))
               => (forall a. (constr a,Typeable a) => g a -> f (g a)) -> c -> f c
traverseCell1' f = cell (traverseCell1 f)

traverseInst :: Functor f 
             => (constr a => a -> f a)
             -> Inst constr a -> f (Inst constr a)
traverseInst f = traverseInst1 $ _Wrapped f

traverseInst1 :: Functor f 
              => (constr a => g a -> f (h a))
              -> Inst1 g constr a -> f (Inst1 h constr a)
traverseInst1 f (Inst x) = Inst <$> f x

mapCell :: (forall a. (constr a,Typeable a) => a -> a) -> Cell constr -> Cell constr
mapCell = mapCell'

mapCell' :: HasCell c (Cell constr)
         => (forall a. (constr a,Typeable a) => a -> a) 
         -> c -> c
mapCell' f = mapCell1' $ _Wrapped %~ f

mapCell1 :: (forall a. (constr a,Typeable a) => f a -> f a) 
         -> Cell1 f constr -> Cell1 f constr
mapCell1 = mapCell1'

mapCell1' :: HasCell c (Cell1 f constr)
          => (forall a. (constr a,Typeable a) => f a -> f a) 
          -> c -> c
mapCell1' f = runIdentity . traverseCell1' (Identity . f)

mapInst :: (constr a => a -> a) 
        -> Inst constr a -> Inst constr a
mapInst f = mapInst1 $ _Wrapped %~ f

mapInst1 :: (constr a => f a -> f a) 
         -> Inst1 f constr a -> Inst1 f constr a
mapInst1 f = runIdentity . traverseInst1 (Identity . f)

readCell1 :: (forall a. (constr a,Typeable a) => f a -> r) -> Cell1 f constr -> r
readCell1 = readCell1'

readCell1' :: HasCell c (Cell1 f constr)
           => (forall a. (constr a,Typeable a) => f a -> r) 
           -> c -> r
readCell1' f = getConst . traverseCell1' (Const . f)

readCell :: (forall a. (constr a,Typeable a) => a -> r) 
         -> Cell constr -> r
readCell f = getConst . traverseCell (Const . f)

readCell' :: HasCell c (Cell constr)
          => (forall a. (constr a,Typeable a) => a -> r) 
          -> c -> r
readCell' f x = readCell f $ x^.cell

readInst :: (constr a => a -> r) 
         -> Inst constr a -> r
readInst f = readInst1 $ f . runIdentity

readInst1 :: (constr a => f a -> r) 
          -> Inst1 f constr a -> r
readInst1 f = getConst . traverseInst1 (Const . f)

-- |
-- = Combinators =

class (c0 a,c1 a) => (c0 :&: c1) a where
instance (c0 a,c1 a) => (c0 :&: c1) a where

apply2Cells :: Functor f
            => (forall a. (constr a,Typeable a) 
                    => a -> a -> f a) 
            -> f (Cell constr) 
            -> Cell constr -> Cell constr 
            -> f (Cell constr)
apply2Cells f = apply2Cells1 (\(Identity x) (Identity y) -> Identity <$> f x y)

apply2Cells' :: (Functor f,HasCell c (Cell constr))
             => (forall a. (constr a,Typeable a) 
                     => a -> a -> f a) 
             -> f c -> c -> c -> f c
apply2Cells' f def x y = view (from cell) <$> apply2Cells f (view cell <$> def) (x^.cell) (y^.cell)

apply2Cells1 :: (Functor f,Typeable g)
             => (forall a. (constr a,Typeable a) 
                     => g a -> g a -> f (g a))
             -> f (Cell1 g constr) 
             -> Cell1 g constr -> Cell1 g constr 
             -> f (Cell1 g constr)
apply2Cells1 f def (Cell x) (Cell y) = fromMaybe def $ fmap Cell . f x <$> cast y

apply2Cells1' :: (Functor f,Typeable g,HasCell c (Cell1 g constr))
              => (forall a. (constr a,Typeable a) 
                      => g a -> g a -> f (g a))
              -> f c 
              -> c -> c
              -> f c
apply2Cells1' f def x y = view (from cell) <$> apply2Cells1 f (view cell <$> def) (x^.cell) (y^.cell)

map2Cells :: (forall a. (constr a,Typeable a) 
                  => a -> a -> a) 
          -> Cell constr -> Cell constr -> Cell constr 
          -> Cell constr 
map2Cells f def x y = runIdentity $ apply2Cells (fmap pure . f) (pure def) x y

map2Cells' :: HasCell c (Cell constr) 
           => (forall a. (constr a,Typeable a) 
                   => a -> a -> a) 
           -> c -> c -> c -> c 
map2Cells' f def x y = view (from cell) $ map2Cells f (def^.cell) (x^.cell) (y^.cell)

map2Cells1 :: (forall a. (constr a,Typeable a) 
                   => a -> a -> a) 
           -> Cell constr -> Cell constr -> Cell constr 
           -> Cell constr 
map2Cells1 f def x y = runIdentity $ apply2Cells (fmap pure . f) (pure def) x y

map2Cells1' :: HasCell c (Cell constr) 
            => (forall a. (constr a,Typeable a) 
                    => a -> a -> a) 
            -> c -> c -> c -> c 
map2Cells1' f def x y = view (from cell) $ map2Cells f (def^.cell) (x^.cell) (y^.cell)


read2CellsWith :: (forall a. (constr a,Typeable a) => a -> a -> r) -> r -> Cell constr -> Cell constr -> r
read2CellsWith f = read2Cells1With $ onIdentity f

read2CellsWith' :: HasCell c (Cell constr)
                => (forall a. (constr a,Typeable a) => a -> a -> r) 
                -> r -> c -> c -> r
read2CellsWith' f def x y = read2CellsWith f def (x^.cell) (y^.cell)

read2Cells1With :: Typeable f
                => (forall a. (constr a,Typeable a) => f a -> f a -> r) 
                -> r -> Cell1 f constr -> Cell1 f constr -> r
read2Cells1With f x = fmap getConst . apply2Cells1 (fmap Const . f) (Const x)

read2Cells1With' :: (HasCell c (Cell1 f constr),Typeable f)
                 => (forall a. (constr a,Typeable a) => f a -> f a -> r) 
                 -> r -> c -> c -> r
read2Cells1With' f def x y = read2Cells1With f def (x^.cell) (y^.cell)

-- |
-- = Heterogenous Combinators

read2CellsH :: (forall a b. (constr a,Typeable a,constr b,Typeable b) => a -> b -> r) 
            -> Cell constr -> Cell constr -> r
read2CellsH f (Cell x) (Cell y) = f (runIdentity x) (runIdentity y)

read2CellsH' :: HasCell c (Cell constr)
             => (forall a b. (constr a,Typeable a,constr b,Typeable b) => a -> b -> r) 
             -> c -> c -> r
read2CellsH' f x y = read2CellsH f (x^.cell) (y^.cell)

read2Cells1H :: (forall a b. (constr a,Typeable a,constr b,Typeable b) => f a -> f b -> r) 
             -> Cell1 f constr -> Cell1 f constr -> r
read2Cells1H f (Cell x) (Cell y) = f x y

read2Cells1H' :: (forall a b. (constr a,Typeable a,constr b,Typeable b) => f a -> f b -> r) 
              -> Cell1 f constr -> Cell1 f constr -> r
read2Cells1H' f x y = read2Cells1H f (x^.cell) (y^.cell)

-- |
-- = Comparing the content of cells

cell1Equal :: Typeable f
           => (forall a. constr a => f a -> f a -> Bool)
           -> Cell1 f constr 
           -> Cell1 f constr 
           -> Bool
cell1Equal f = read2Cells1With f False

cell1Equal' :: (HasCell c (Cell1 f constr),Typeable f)
            => (forall a. constr a => f a -> f a -> Bool)
            -> c -> c -> Bool
cell1Equal' f x y = cell1Equal f (x^.cell) (y^.cell)

cellEqual :: (forall a. constr a => a -> a -> Bool)
          -> Cell constr 
          -> Cell constr 
          -> Bool
cellEqual f = read2CellsWith f False

cellEqual' :: HasCell c (Cell constr) 
           => (forall a. constr a => a -> a -> Bool)
           -> c -> c -> Bool
cellEqual' f x y = cellEqual f (x^.cell) (y^.cell)


cellCompare :: (forall a. constr a => a -> a -> Ordering)
            -> Cell constr 
            -> Cell constr 
            -> Ordering
cellCompare = cellCompare'

cellCompare' :: HasCell c (Cell constr) 
             => (forall a. constr a => a -> a -> Ordering)
             -> c -> c -> Ordering
cellCompare' f = cell1Compare' $ onIdentity f

cell1Compare :: (Typeable f)
             => (forall a. constr a => f a -> f a -> Ordering)
             -> Cell1 f constr 
             -> Cell1 f constr 
             -> Ordering
cell1Compare f x y = read2Cells1With f (x' `compare` y') x y
    where
        x' = readCell1 typeOf x :: TypeRep
        y' = readCell1 typeOf y :: TypeRep

cell1Compare' :: (HasCell c (Cell1 f constr),Typeable f)
              => (forall a. constr a => f a -> f a -> Ordering)
              -> c -> c -> Ordering
cell1Compare' f x y = cell1Compare f (x^.cell) (y^.cell)

-- |
-- = Creating Lenses

cellLens :: Functor f => (forall a. constr a => LensLike' f a b) -> LensLike' f (Cell constr) b
cellLens = cellLens'

cellLens' :: (HasCell c (Cell constr), Functor f)
          => (forall a. constr a => LensLike' f a b) 
          -> LensLike' f c b
cellLens' ln f = traverseCell' (ln f)

cell1Lens :: Functor f 
          => (forall a. constr a => LensLike' f (g a) b) 
          -> LensLike' f (Cell1 g constr) b
cell1Lens = cell1Lens'

cell1Lens' :: (HasCell c (Cell1 g constr), Functor f)
           => (forall a. constr a => LensLike' f (g a) b) 
           -> LensLike' f c b
cell1Lens' ln f = traverseCell1' (ln f)

-- |
-- = Change type classes

rewriteCell :: EntailsAll c0 c1 
            -> Cell1 f c0
            -> Cell1 f c1
rewriteCell d (Cell x) = case spec x d of Sub D -> (Cell x)

rewriteInst :: c0 a :- c1 a
            -> Inst1 f c0 a
            -> Inst1 f c1 a
rewriteInst d (Inst x) = case spec x d of Sub D -> (Inst x)

spec :: f a -> p a :- q a -> p a :- q a
spec _ = id

transEnt :: EntailsAll c0 c1 
         -> EntailsAll c1 c2
         -> EntailsAll c0 c2
transEnt = flip (.)

ordEntailsEq :: EntailsAll Ord Eq
ordEntailsEq = Sub D

exArrow :: forall m cl f b.
           (forall a. Kleisli m (Inst1 f cl a) b)
        -> Kleisli m (Cell1 f cl) b
exArrow m = Kleisli $ getConst . asInst1 m'
  where
    m' :: forall a. Inst1 f cl a -> Const (m b) (Inst1 f cl a)
    m' = Const . runKleisli m

-- |
-- = QuickCheck Helpers

arbitraryCell :: Name -> ExpQ
arbitraryCell cl = arbitraryCell' cl []

arbitraryCell' :: Name -> [TypeQ] -> ExpQ
arbitraryCell' cl ts = [e| $(arbitraryInstanceOf' 'Cell cl ts) :: Gen (Cell $(conT cl)) |]

arbitraryInstanceOf :: Name -> Name -> ExpQ
arbitraryInstanceOf cons cl = arbitraryInstanceOf' cons cl []

arbitraryInstanceOf' :: Name -> Name -> [TypeQ] -> ExpQ
arbitraryInstanceOf' cons cl ts = do
        ClassI _ is <- reify cl
        ts <- sequence ts
        let getArg (InstanceD [] (AppT _ t) []) 
                | t `notElem` ts = return (Just t)
                | otherwise      = return Nothing
            getArg t = do
                reportError $ "invalid number of arguments in instance: " ++ pprint t
                return Nothing
            --trigger x = 

        is' <- catMaybes <$> mapM (fmap (fmap return) . getArg) is
        let arbits = [ [e| $(conE cons) . pure <$> $(arb i) |] | i <- is' ]
            arb i  = sigE [e| arbitrary |] [t| Gen $i |]
        when (null is') $ fail $ printf "no instances of '%s' found" (show cl)
        [e| oneof $(listE arbits) |]

-- |
-- = Utilities

-- | Utility function to facilitate the implementation of 'Cell'
-- | functions in terms of 'Cell1' functions.
onIdentity :: (a -> b -> c) 
           -> Identity a -> Identity b
           -> c
onIdentity f (Identity x) (Identity y) = f x y

-- |
-- = Properties

-- | Wrapping two values in cells does not change their equality
prop_consistent_equal :: (Eq a,Typeable a) => a -> a -> Property
prop_consistent_equal x y = cellEqual (==) (makeCell' x) (makeCell' y) === (x == y)
    where
      makeCell' = makeCell :: (Eq a,Typeable a) => a -> Cell Eq

-- | Wrapping two values in cells does not change their relative order
prop_consistent_compare :: (Ord a,Typeable a) => a -> a -> Property
prop_consistent_compare x y = cellCompare compare (makeCell' x) (makeCell' y) === (x `compare` y)
    where
      makeCell' = makeCell :: (Ord a,Typeable a) => a -> Cell Ord

return []

-- | Check all the QuickCheck properties.
run_tests :: IO Bool
run_tests = $quickCheckAll
