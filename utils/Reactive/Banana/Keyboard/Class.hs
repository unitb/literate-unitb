{-# LANGUAGE TypeFamilies #-}
module Reactive.Banana.Keyboard.Class where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Trans.Lens
import Control.Monad.Writer

import Data.Typeable

import Reactive.Banana

class Monad m => KeyboardMonad m where
    command' :: forall a. (Typeable a,Show a,Read a) 
             => Behavior String
             -> m (Event a)
    specializeKeyboard :: Behavior String
                       -> m a
                       -> m a

        -- Defaults
    default command' :: forall a t m'. 
                        ( Typeable a,Show a,Read a
                        , MonadTrans t, KeyboardMonad m', t m' ~ m) 
                     => Behavior String
                     -> t m' (Event a)
    command' = lift . command'
    default specializeKeyboard :: (MonadFunTrans t, KeyboardMonad m', t m' ~ m)
                               => Behavior String
                               -> t m' a
                               -> t m' a
    specializeKeyboard b = insideM %~ specializeKeyboard b

instance KeyboardMonad m => KeyboardMonad (ReaderT r m) where
instance KeyboardMonad m => KeyboardMonad (StateT s m) where
instance (KeyboardMonad m,Monoid w) => KeyboardMonad (WriterT w m) where
instance (KeyboardMonad m,Monoid w) => KeyboardMonad (RWST r w s m) where
