module Data.Unfoldable where

import Data.Functor.Identity
import Data.List.NonEmpty
import Data.Proxy

type None = Proxy
type One  = Identity

class Unfoldable t where
    expectedSize :: Proxy t -> String
    unfoldM :: Monad m
            => (a -> m (Maybe (b,a)))
            -> a 
            -> m (Maybe (t b))

unfold :: Unfoldable t 
       => (a -> Maybe (b,a))
       -> a 
       -> Maybe (t b)
unfold f = runIdentity . unfoldM (Identity . f)

instance Unfoldable None where
    expectedSize _ = "zero"
    unfoldM _ _ = pure $ Just $ Proxy
instance Unfoldable One where
    expectedSize _ = "exactly one"
    unfoldM f x = fmap (Identity . fst) <$> f x
instance Unfoldable [] where
    expectedSize _ = "any number"
    unfoldM f x = Just <$> unfoldM' f x
instance Unfoldable Maybe where
    expectedSize _ = "zero or one"
    unfoldM f x = Just . fmap fst <$> f x
instance Unfoldable NonEmpty where
    expectedSize _ = "at least one"
    unfoldM f x = do
        r <- f x
        case r of
            Just (y,x) -> Just . (y:|) <$> unfoldM' f x
            Nothing -> return Nothing 

unfoldM' :: Monad m
         => (a -> m (Maybe (b, a))) 
         -> a -> m [b]
unfoldM' f x = f' =<< f x
    where 
        f' Nothing = return []
        f' (Just (y,x)) = (y:) <$> unfoldM' f x
