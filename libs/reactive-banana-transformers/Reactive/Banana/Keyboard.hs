{-# LANGUAGE RankNTypes,ScopedTypeVariables,UndecidableInstances #-}
module Reactive.Banana.Keyboard where

import Reactive.Banana
import Reactive.Banana.Frameworks

import Control.Lens hiding (pre)
import Control.Monad.Reader
import Control.Monad.RWS

import Data.Functor.Compose
import Data.List.Lens
import Data.Semigroup.Applicative
import Data.String.Utils hiding (split)
import Data.Typeable
import Data.Typeable.Lens

import Reactive.Banana.IO

import Text.Printf.TH

type Keyboard = KeyboardT Moment
type KeyboardIO = KeyboardT MomentIO
type Filter   = Behavior [String]
newtype KeyboardT m a = Keyboard { _keyboard :: RWST Filter (Ap Behavior [String]) (Event String) m a }
    deriving ( Functor, Applicative
             , MonadTrans
             , MonadIO, MonadMoment
             , MonadMomentIO
             , MonadFix )

instance Monad m => Monad (KeyboardT m) where
    {-# INLINE (>>=) #-}
    Keyboard m >>= f = Keyboard $ m >>= _keyboard . f

makeLenses ''KeyboardT

class KeyboardMonad m where
    command' :: forall a. (Typeable a,Show a,Read a) 
             => Behavior String
             -> m (Event a)
    specializeKeyboard :: Behavior String
                       -> m a
                       -> m a


instance Monad m => KeyboardMonad (KeyboardT m) where
    specializeKeyboard f (Keyboard m) = Keyboard $ local (liftA2 (:) f) m
    command' name = Keyboard $ do
        pre <- ask
        kb <- get
        let cmd  = concat.reverse <$> liftA2 (:) name pre
            arg  = matching.(._Show').prefixed <$> cmd <@> kb
            arg' = Compose arg
            (kb',r) = split arg
        tell $ Ap $ sequenceA [liftA2 (++) cmd $ pure $ show $ typeRep arg']
        --state (split . fmap (swapEither . matching (_.pr)))
        put kb'
        return r

_Show' :: (Read a,Show a,Typeable a) => Prism' String a
_Show' = prism' show (\x -> x^?prefixed " ".to strip._Show <|> x^?to strip.only ""._cast)
    -- prism (view chosen) _.without _Show _

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

withKeyboardT :: (Functor m)
              => Event String
              -> KeyboardT m a
              -> m (a,Event String,Behavior [String])
withKeyboardT kb m = (_3 %~ getAp) <$> runRWST (m^.keyboard) (pure []) kb

withKeyboard_ :: MonadMomentIO m
              => Event String
              -> KeyboardT m a
              -> m a
withKeyboard_ e m = do
        (x,kb,cmds) <- withKeyboardT e m
        reject kb cmds
        return x

combine :: ReifiedPrism s t a b
        -> ReifiedPrism a b a' b'
        -> ReifiedPrism s t a' b'
combine (Prism p0) (Prism p1) = Prism $ p0 . p1

reject :: MonadMomentIO m
       => Event String
       -> Behavior [String]
       -> m ()
reject kb cmds = do
    let msg = flip [printf|Invalid command: '%s'\nValid commands:\n%s\n|] . unlines . map ("  " ++)
    liftMomentIO $ reactimate $ fmap putStrLn . msg <$> cmds <@> kb

command :: (KeyboardMonad m,Read a,Show a,Typeable a)
        => String
        -> m (Event a)
command cmd = command' $ pure cmd
