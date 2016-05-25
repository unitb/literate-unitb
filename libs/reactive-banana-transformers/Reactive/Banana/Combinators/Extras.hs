{-# LANGUAGE DataKinds,TypeOperators,ScopedTypeVariables,TypeFamilies #-}
module Reactive.Banana.Combinators.Extras where

import Control.Lens
import Control.Monad
import Control.Precondition

import Data.These
import Data.Proxy.TH
import Data.Semigroup
import Data.TypeList

import Reactive.Banana

unionsWith :: (a -> a -> a) -> [Event a] -> Event a
unionsWith f (x:xs) = foldl (unionWith f) x xs
unionsWith _ []     = never

unionsM :: Monad m => [Event (a -> m a)] -> Event (a -> m a)
unionsM = unionsWith (>=>)

unions' :: Semigroup m => [Event m] -> Event m
unions' = unionsWith (<>)

union' :: Semigroup m => Event m -> Event m -> Event m
union' = unionWith (<>)

eventPair :: Event a -> Event b -> Event (Maybe a,Maybe b)
eventPair e0 e1 = f <$> eventPair' e0 e1
    where
      f (This x) = (Just x,Nothing)
      f (That y) = (Nothing,Just y)
      f (These x y) = (Just x,Just y)

eventPair' :: Event a -> Event b -> Event (These a b)
eventPair' e0 e1 = unionWith mappend'
                        (This <$> e0) 
                        (That <$> e1)
    where
        mappend' (This x) (That y) = These x y
        mappend' _ _ = undefined'

intersection :: Event a -> Event b -> Event (a,b)
intersection = intersectionWith (,)

intersectionWith :: (a -> b -> c)
                 -> Event a -> Event b -> Event c
intersectionWith f = eventPair & mapped.mapped %~ \e ->
        e & mapped %~ uncurry (liftA2 f)
          & filterJust


between :: (MonadMoment m)
        => Event a -> Event b -> m (Behavior Bool)
between e0 e1 = do
        stepper False (unionWith const (False <$ e1) (True <$ e0))

uncurriedEvent' :: ( Curried t r f
                   , AsTypeList t Event
                   , t' ~ ReplaceF Maybe t
                   , AsTypeList t' Maybe
                   , TypeListOf t ~ TypeListOf t')
                => Iso' f (Event t' -> r)
uncurriedEvent' = uncurried'.lmapping (mapping asTypeList'.splittingEventList.from asTypeList')

uncurriedEvent :: ( Curried tE r f,AsTypeList tE Event,AsTypeList t Maybe
                  , Curried tE' r' f',AsTypeList tE' Event,AsTypeList t' Maybe
                  , t ~ ReplaceF Maybe tE
                  , t' ~ ReplaceF Maybe tE'
                  , TypeListOf tE ~ TypeListOf t
                  , TypeListOf tE' ~ TypeListOf t')
               => Iso f f' (Event t -> r) (Event t' -> r')
uncurriedEvent = withIso uncurriedEvent' 
                      $ \f _ -> withIso uncurriedEvent' 
                      $ \_ f' -> iso f f'

curriedEvent :: ( Curried tE r f,AsTypeList tE Event,AsTypeList t Maybe
                , Curried tE' r' f',AsTypeList tE' Event,AsTypeList t' Maybe
                , t ~ ReplaceF Maybe tE
                , t' ~ ReplaceF Maybe tE'
                , TypeListOf tE ~ TypeListOf t 
                , TypeListOf tE' ~ TypeListOf t')
             => Iso (Event t -> r) (Event t' -> r') f f'
curriedEvent = from uncurriedEvent

curriedEvent' :: ( Curried t r f,AsTypeList t Event,AsTypeList t' Maybe
                 , t' ~ ReplaceF Maybe t
                 , TypeListOf t ~ TypeListOf t')
              => Iso' (Event t' -> r) f
curriedEvent' = from uncurriedEvent'

joinEventList :: forall as. IsTypeList as
              => List' Event as
              -> Event (List' Maybe as)
joinEventList = byCase
        ( (\Null -> never)
          :: List' Event '[] -> Event (List' Maybe '[]) )
        ( (\(Cons' e es) -> unionWith (zipWithL' (<|>)) 
                           ((\x -> Cons' (Just x) (replicateL Nothing)) <$> e) 
                           (Cons' Nothing <$> joinEventList es))
          :: IsTypeList as1 => (List' Event (a ': as1) -> Event (List' Maybe (a ': as1))) )
        [pr|as|]
splitEventList :: forall as. IsTypeList as
               => Event (List' Maybe as)
               -> List' Event as
splitEventList e = byCase 
        Null 
        (Cons' (filterJust $ headL <$> e) (splitEventList $ tailL <$> e)) 
        [pr|as|]

splittingEventList :: IsTypeList as => Iso' (Event (List' Maybe as)) (List' Event as)
splittingEventList = iso splitEventList joinEventList

packageEventFun' :: forall t r' f m. 
                    ( Curried (ReplaceF Event t) (m (ReplaceF Event r')) f
                    , AsTypeList r' Maybe
                    , AsTypeList t Maybe 
                    , AsTypeList (ReplaceF Event r') Event
                    , AsTypeList (ReplaceF Event t) Event
                    , TypeListOf t ~ TypeListOf (ReplaceF Event t)
                    , TypeListOf (ReplaceF Event r') ~ TypeListOf r'
                    , Functor m, ReplaceF Maybe (ReplaceF Event t) ~ t)
                 => Iso' f (Event t -> m (Event r'))
packageEventFun' = iso0 . iso1
    where
      iso0 :: Iso' f (Event t -> m (ReplaceF Event r'))
      iso0 = uncurriedEvent'
      iso1 :: Iso' (Event t -> m (ReplaceF Event r')) (Event t -> m (Event r'))
      iso1 = mapping (mapping $ from splittingEvent')

splittingEvent :: ( SameLength t0 t1, AsTypeList t0 Maybe
                  , SameLength t0 t0', AsTypeList t0' Maybe
                  , SameLength t0' t1'
                  , AsTypeList t1 Event
                  , AsTypeList t1' Event )
               => Iso (Event t0) (Event t0') t1 t1'
splittingEvent = withIso splittingEvent' 
                      $ \f _  -> withIso splittingEvent'
                      $ \_ f' -> iso f f'

splittingEvent' :: ( SameLength t0 t1
                   -- , t0 ~ ReplaceF Maybe t1
                   -- , t1 ~ ReplaceF Event t0
                   , AsTypeList t0 Maybe
                   , AsTypeList t1 Event )
                => Iso' (Event t0) t1
splittingEvent' = mapping asTypeList.splittingEventList.from asTypeList

joiningEvent :: ( SameLength t0 t1, AsTypeList t0 Maybe
                , SameLength t0 t0', AsTypeList t0' Maybe
                , SameLength t0' t1'
                , AsTypeList t1 Event
                , AsTypeList t1' Event )
             => Iso t1 t1' (Event t0) (Event t0')
joiningEvent = from splittingEvent

joiningEvent' :: ( SameLength t0 t1
                 , AsTypeList t0 Maybe
                 , AsTypeList t1 Event )
              => Iso' t1 (Event t0)
joiningEvent' = from splittingEvent'
