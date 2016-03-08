module Reactive.Banana.Discrete where

import Reactive.Banana

data Discrete a = Discrete a (Event a)
    deriving Functor

-- instance Applicative Discrete where
--     pure x = Discrete x never (pure x)
--     Discrete f eF bF <*> Discrete x eX bX = Discrete y eY bY
--         where
--             y  = f x
--             eY = unionWith const (bF <@> eX) (flip id <$> bX <@> eF)
--             bY = bF <*> bX

stepperD :: a -> Event a 
         -> Discrete a
stepperD = Discrete

valueD :: Discrete a -> a
valueD (Discrete x _) = x

changesD :: Discrete a -> Event a
changesD (Discrete _ ev) = ev

accumD :: MonadMoment m
       => a
       -> Event (a -> a)
       -> m (Discrete a)
accumD x ev = stepperD x <$> accumE x ev

mapAccumD :: MonadMoment m
          => acc -> Event (acc -> (x, acc)) 
          -> m (Event x, Discrete acc)
mapAccumD acc ef = do
        e <- accumE  (undefined,acc) (lift <$> ef)
        let b = stepperD acc (snd <$> e)
        return (fst <$> e, b)
    where
        lift f (_,acc) = acc `seq` f acc

behavior :: MonadMoment m
         => Discrete a -> m (Behavior a)
behavior (Discrete x ev) = stepper x ev
