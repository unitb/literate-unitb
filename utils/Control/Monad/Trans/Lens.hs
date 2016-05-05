{-# LANGUAGE TypeFamilies #-}
module Control.Monad.Trans.Lens where

import Control.Applicative
import Control.Lens

import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

class MonadTrans t => MonadFunTrans t where
    insideM :: Monad m => Setter (t m a) (t m b) (m a) (m b)

instance Monoid w => MonadFunTrans (RWST r w s) where
    insideM = insideRWST
instance MonadFunTrans (ReaderT r) where
    insideM = insideReaderT
instance MonadFunTrans (StateT s) where
    insideM = insideStateT
instance Monoid w => MonadFunTrans (WriterT w) where
    insideM = insideWriterT

insideRWST :: Applicative m
           => Setter (RWST r w s m a) (RWST r w s m b) (m a) (m b)
insideRWST = _Wrapped . mapped . mapped . mapping' _1

insideReaderT :: Setter (ReaderT r m a) (ReaderT r m b) (m a) (m b)
insideReaderT = _Wrapped . mapped

insideStateT :: Applicative m
             => Setter (StateT s m a) (StateT s m b) (m a) (m b)
insideStateT = _Wrapped . mapped . mapping' _1

insideWriterT :: Applicative m
              => Setter (WriterT r m a) (WriterT r m b) (m a) (m b)
insideWriterT = _Wrapped . mapping' _1

mapping' :: Applicative f
         => Lens s t a b -> Lens (f s) (f t) (f a) (f b)
mapping' ln = lens (fmap f) $ liftA2 (flip $ set ln)
    where
        f = getConst . ln Const

asState :: Applicative m
        => Setter (RWST r w s m a) (RWST r w s m b) (StateT s m a) (StateT s m b)
asState = _Wrapped.mapped.inside (mapping' $ lens dropLast setLast)._Unwrapped
    where
        dropLast (x,y,_) = (x,y)
        setLast (_,_,w) (b,s) = (b,s,w)

asWriter :: Applicative m
         => Setter (RWST r w s m a) (RWST r w s m b) (WriterT w m a) (WriterT w m b)
asWriter = _Wrapped.mapped.mapped.mapping' (lens dropMiddle setMiddle)._Unwrapped
    where
        dropMiddle (x,_,y) = (x,y)
        setMiddle (_,m,_) (x,y) = (x,m,y)

asReader :: Applicative m
         => Setter (RWST r w s m a) (RWST r w s m b) (ReaderT r m a) (ReaderT r m b)
asReader = _Wrapped.flipped.mapped.inside (mapping' $ lens dropTail setTail)._Unwrapped
    where
        dropTail (x,_,_) = x
        setTail (_,x,y) a = (a,x,y)
