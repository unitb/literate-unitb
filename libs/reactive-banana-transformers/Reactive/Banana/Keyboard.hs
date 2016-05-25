{-# LANGUAGE RankNTypes,ScopedTypeVariables
    ,UndecidableInstances,TypeFamilies #-}
module Reactive.Banana.Keyboard where

import Reactive.Banana
import Reactive.Banana.Frameworks

import Control.Lens hiding (pre)
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.Trans.Lens

import Data.Functor.Compose
import Data.List.Lens
import Data.Semigroup.Applicative
import Data.String.Utils hiding (split)
import Data.Typeable
import Data.Typeable.Lens

import Reactive.Banana.IO

import Text.Printf.TH

type Keyboard = KeyboardT Moment
data KeyboardEvents a = KeyboardEvents [String] [Maybe [String]] [Maybe String] a
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

instance Frameworks m => Frameworks (KeyboardT m) where
    type EventList (KeyboardT m) a = EventList m (Maybe [String],Maybe String,Maybe a)
    type InitF (KeyboardT m) = ([String],InitF m)
    interpret' = interpretKeyboard

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

-- instance Frameworks m i o => Frameworks (KeyboardT m) i o where
--     interpret' x f xs = do 
--         id <$> interpret' (_ x) (fmap id . _keyboard . f) xs

interpretKeyboard :: forall m a b. (Frameworks m)
                  => (Event a -> KeyboardT m (Event b))
                  -> ([String],InitF m)
                  -- -> [(Maybe [String],Maybe String,Maybe (EventList m a))]
                  -> [EventList m (Maybe [String],Maybe String,Maybe a)]
                  -> IO ([EventList m (Maybe [String],Maybe String,Maybe a)],[Maybe b])
interpretKeyboard f (xs,i) = interpret' f' i
  where
    f' :: Event (Maybe [String],Maybe String,Maybe a) -> m (Event b)
    f' e = do
      cmdFilter <- stepper xs $ filterJust (view _1 <$> e)
      let arg = filterJust (view _3 <$> e)
          kbInput = filterJust (view _2 <$> e)
      view _1 <$> runRWST (_keyboard . f $ arg) cmdFilter kbInput

_Show' :: (Read a,Show a,Typeable a) => Prism' String a
_Show' = prism' show (\x -> x^?prefixed " ".to strip._Show <|> x^?to strip.only ""._cast)
    -- prism (view chosen) _.without _Show _

-- overA :: Lens' s t a b -> (arr a b) -> (arr s t)
-- overA ln = proc x -> do

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
