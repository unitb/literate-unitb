{-# LANGUAGE KindSignatures
    ,ConstraintKinds
    ,ExistentialQuantification
    #-}
module Utilities.Existential where

import Control.Applicative as A
import Control.Lens
import Control.Monad

import Data.Maybe
import Data.Typeable

import GHC.Exts (Constraint)

import Language.Haskell.TH

import Test.QuickCheck

import Text.Printf

data Cell (constr :: * -> Constraint) = forall a. (constr a, Typeable a) => Cell a

class HasCell a b | a -> b where
    cell :: Iso' a b

makeCell :: (HasCell a (Cell constr), constr b, Typeable b)
         => b -> a
makeCell x = Cell x ^. from cell

instance HasCell (Cell constr) (Cell constr) where
    cell = id

_Cell :: (constr b,Typeable b,Typeable a) => Prism (Cell constr) (Cell constr) a b
_Cell = prism Cell $ \x -> maybe (Left x) Right $ readCell cast x

_Cell' :: (constr a,Typeable a) => Prism (Cell constr) (Cell constr) a a
_Cell' = _Cell

asCell :: (constr a,Typeable a,HasCell c (Cell constr)) => Prism c c a a
asCell = cell._Cell'

traverseCell :: Functor f => (forall a. (constr a,Typeable a) => a -> f a) 
             -> Cell constr -> f (Cell constr)
traverseCell f (Cell x) = Cell <$> f x

traverseCell' :: (Functor f,HasCell c (Cell constr))
              => (forall a. (constr a,Typeable a) => a -> f a) -> c -> f c
traverseCell' f = cell (traverseCell f)

mapCell :: (forall a. (constr a,Typeable a) => a -> a) -> Cell constr -> Cell constr
mapCell f = runIdentity . traverseCell (Identity . f)

mapCell' :: HasCell c (Cell constr)
         => (forall a. (constr a,Typeable a) => a -> a) 
         -> c -> c
mapCell' f x = mapCell f (x^.cell) ^. from cell

readCell :: (forall a. (constr a,Typeable a) => a -> r) -> Cell constr -> r
readCell f = getConst . traverseCell (Const . f)

readCell' :: HasCell c (Cell constr)
          => (forall a. (constr a,Typeable a) => a -> r) 
          -> c -> r
readCell' f x = readCell f $ x^.cell

apply2Cells :: Functor f
            => (forall a. (constr a,Typeable a) 
                    => a -> a -> f a) 
            -> f (Cell constr) 
            -> Cell constr -> Cell constr 
            -> f (Cell constr)
apply2Cells f def (Cell x) (Cell y) = fromMaybe def $ fmap Cell . f x <$> cast y

apply2Cells' :: (Functor f,HasCell c (Cell constr))
             => (forall a. (constr a,Typeable a) 
                     => a -> a -> f a) 
             -> f c -> c -> c -> f c
apply2Cells' f def x y = view (from cell) <$> apply2Cells f (view cell <$> def) (x^.cell) (y^.cell)

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

read2CellsWith :: (forall a. (constr a,Typeable a) => a -> a -> r) -> r -> Cell constr -> Cell constr -> r
read2CellsWith f def (Cell x) (Cell y) = fromMaybe def $ f x <$> cast y

read2CellsWith' :: HasCell c (Cell constr)
                => (forall a. (constr a,Typeable a) => a -> a -> r) 
                -> r -> c -> c -> r
read2CellsWith' f def x y = read2CellsWith f def (x^.cell) (y^.cell)

read2CellsH :: (forall a b. (constr a,Typeable a,constr b,Typeable b) => a -> b -> r) 
            -> Cell constr -> Cell constr -> r
read2CellsH f (Cell x) (Cell y) = f x y

read2CellsH' :: HasCell c (Cell constr)
             => (forall a b. (constr a,Typeable a,constr b,Typeable b) => a -> b -> r) 
             -> c -> c -> r
read2CellsH' f x y = read2CellsH f (x^.cell) (y^.cell)

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
cellCompare f x y = read2CellsWith f (x' `compare` y') x y
    where
        x' = readCell typeOf x :: TypeRep
        y' = readCell typeOf y :: TypeRep

cellCompare' :: HasCell c (Cell constr) 
             => (forall a. constr a => a -> a -> Ordering)
             -> c -> c -> Ordering
cellCompare' f x y = cellCompare f (x^.cell) (y^.cell)

cellLens :: Functor f => (forall a. constr a => LensLike' f a b) -> LensLike' f (Cell constr) b
cellLens ln f = traverseCell (ln f)

cellLens' :: (HasCell c (Cell constr), Functor f)
          => (forall a. constr a => LensLike' f a b) 
          -> LensLike' f c b
cellLens' ln = cell.cellLens ln

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
        let arbits = [ [e| $(conE cons) <$> $(arb i) |] | i <- is' ]
            arb i  = sigE [e| arbitrary |] [t| Gen $i |]
        when (null is') $ fail $ printf "no instances of '%s' found" (show cl)
        [e| oneof $(listE arbits) |]

arbitraryCell :: Name -> ExpQ
arbitraryCell cl = arbitraryCell' cl []

arbitraryCell' :: Name -> [TypeQ] -> ExpQ
arbitraryCell' cl ts = [e| $(arbitraryInstanceOf' 'Cell cl ts) :: Gen (Cell $(conT cl)) |]
