module Reactive.Banana.Monitor where

import Control.Arrow hiding ((<+>))
import Control.Lens hiding ((<&>))

import Data.Maybe
import Data.String.Lines

import Reactive.Banana
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.IO

data Monitor a = Monitor a (Event a) 
    deriving (Functor)

getEvent :: Monitor a -> Event a
getEvent (Monitor _ e) = e

(<&>) :: (Maybe a -> b) -> Event a -> Monitor b
(<&>) f e = pure f <+> e

(<+>) :: Monitor (Maybe a -> b) -> Event a -> Monitor b
(<+>) (Monitor v e) e' = Monitor (v Nothing) $ eventPair e e' 
            & mapped._1 %~ fromMaybe v 
            & mapped %~ uncurry ($)

liftE :: (a -> b) 
      -> Event a
      -> Event b
liftE = fmap

liftE2 :: (Maybe a -> Maybe b -> c) 
       -> Event a
       -> Event b
       -> Event c
liftE2 f e0 e1 = getEvent $ f <&> e0 <+> e1

liftE3 :: (Maybe a -> Maybe b -> Maybe c -> d) 
       -> Event a
       -> Event b
       -> Event c
       -> Event d
liftE3 f e0 e1 e2 = getEvent $ f <&> e0 <+> e1 <+> e2

liftE4 :: (Maybe a -> Maybe b -> Maybe c -> Maybe d -> e) 
       -> Event a
       -> Event b
       -> Event c
       -> Event d
       -> Event e
liftE4 f e0 e1 e2 e3 = getEvent $ f <&> e0 <+> e1 <+> e2 <+> e3

liftE5 :: (Maybe a -> Maybe b -> Maybe c -> Maybe d -> Maybe e -> f) 
       -> Event a
       -> Event b
       -> Event c
       -> Event d
       -> Event e
       -> Event f
liftE5 f e0 e1 e2 e3 e4 = getEvent $ f <&> e0 <+> e1 <+> e2 <+> e3 <+> e4

instance Applicative Monitor where
    pure x = Monitor x never
    Monitor f f' <*> Monitor x x' = Monitor (f x) (eventPair f' x' 
                & mapped._1 %~ fromMaybe f 
                & mapped._2 %~ fromMaybe x 
                & mapped %~ uncurry ($))

data Display =  Evt (Event String)
              | Beh (Behavior String) 

disp :: Show a => String -> Event a -> Display
disp msg = dispStr msg . fmap show

dispStr :: String -> Event String -> Display
dispStr msg = Evt . fmap (\x -> concatIndent [msg,": ",x])

disp_ :: String -> Event a -> Display
disp_ msg e = Evt $ msg <$ e

dispB :: Show a => String -> Behavior a -> Display
dispB msg = dispStrB msg . fmap show

dispStrB :: String -> Behavior String -> Display
dispStrB msg = Beh . fmap (\x -> concatIndent ["[ - ",msg,": ",x," ]"])

monitor' :: [Display] -> Event String
monitor' xs = unionsWith cat $ map polled xs
    where
      cat x y = x ++ "\n" ++ y
      eventOf (Evt e) = () <$ e
      eventOf (Beh _) = never
      tick = unionsWith const (map eventOf xs)
      polled (Evt e) = e
      polled (Beh b) = b <@ tick

test :: IO ()
test = do
        let sys e = do
                let (e0,e1) = e & (filterJust . fmap fst &&& filterJust . fmap snd)
                return $ liftE2 (\x y -> show x ++ fromMaybe "" y) e0 e1
        (x,y) <- interpretFrameworks' sys [Just (Just 1,Nothing),Nothing,Just (Nothing,Just "foo"),Just (Just 7,Just "bar")]
        putStrLn "input"
        mapM_ print x
        putStrLn "output"
        mapM_ print y

