{-# LANGUAGE RankNTypes,UndecidableInstances #-}
module Reactive.Banana.Keyboard where

import Reactive.Banana
import Reactive.Banana.Frameworks

import Control.Arrow
import Control.Lens hiding (pre)
import Control.Monad.Reader
import Control.Monad.RWS

import Text.Printf

type Keyboard = KeyboardT Moment
type KeyboardIO = KeyboardT MomentIO
newtype KeyboardT m a = Keyboard { _keyboard :: RWST (Behavior (ReifiedPrism' String String)) () (Event String) m a }
    deriving ( Functor, Applicative
             , Monad, MonadTrans
             , MonadIO, MonadMoment
             , MonadFix )

instance (MonadMoment m,Monoid w) => MonadMoment (RWST r w s m) where
    liftMoment = lift . liftMoment

makeLenses ''KeyboardT

class KeyboardMonad m where
    command' :: Behavior (ReifiedPrism' String a) 
             -> m (Event a)
    specializeKeyboard :: Behavior (ReifiedPrism' String String)
                       -> m a
                       -> m a


instance Monad m => KeyboardMonad (KeyboardT m) where
    specializeKeyboard f (Keyboard m) = Keyboard $ local (\f' -> combine <$> f' <*> f) m
    command' pr = Keyboard $ do
        pre <- ask
        kb <- get
        let cmd = (matching.runPrism) <$> (combine<$>pre<*>pr) <@> kb
            (kb',r) = split cmd
        --state (split . fmap (swapEither . matching (_.pr)))
        put kb'
        return r

-- overA :: Lens' s t a b -> (arr a b) -> (arr s t)
-- overA ln = proc x -> do


insideRWST :: Applicative m
           => Setter (RWST r w s m a) (RWST r w s m b) (m a) (m b)
insideRWST = iso runRWST RWST . mapped . mapped . lens (fmap $ view _1) (liftA2 $ flip $ set _1)

insideReaderT :: Setter (ReaderT r m a) (ReaderT r m b) (m a) (m b)
insideReaderT = iso runReaderT ReaderT . mapped

instance MonadReader r m => MonadReader r (KeyboardT m) where
    reader = lift . reader
    local f = keyboard.insideRWST %~ local f
instance MonadState s m => MonadState s (KeyboardT m) where
    state = lift . state
instance MonadWriter w m => MonadWriter w (KeyboardT m) where
    writer = lift . writer
    listen = keyboard.insideRWST %~ listen
    pass   = keyboard.insideRWST %~ pass

withKeyboard :: (Functor m)
             => Event String
             -> KeyboardT m a
             -> m (a,Event String)
withKeyboard kb m = (view _1 &&& view _2) <$> runRWST (m^.keyboard) (pure $ Prism id) kb

withKeyboard_ :: Event String
              -> KeyboardIO a
              -> MomentIO a
withKeyboard_ e m = do
        (x,kb) <- withKeyboard e m
        reject kb
        return x

combine :: ReifiedPrism s t a b
        -> ReifiedPrism a b a' b'
        -> ReifiedPrism s t a' b'
combine (Prism p0) (Prism p1) = Prism $ p0 . p1

takeKeyboard :: (KeyboardMonad m)
             => m (Event String)
takeKeyboard = do
        command id

reject :: Event String
       -> MomentIO ()
reject kb = do
    reactimate $ printf "Invalid command: '%s'\n" <$> kb

command :: (KeyboardMonad m)
        => Prism' String a
        -> m (Event a)
command = command' . pure . Prism
