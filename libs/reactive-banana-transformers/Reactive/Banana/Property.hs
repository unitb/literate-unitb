{-# LANGUAGE KindSignatures, GADTs, PolyKinds #-}
module Reactive.Banana.Property where

import Control.Arrow
import Control.Exception
import Control.Exception.Lens
import Control.Invariant
import Control.Lens
import Control.Lens.Misc
import Control.Monad.Reader
import Control.Monad.State
import Control.Precondition

import Data.Function
import Data.List as L
import Data.Proxy
import Data.String.Lines
import Data.These
import Data.Time

import Reactive.Banana as R hiding (interpret,apply)
import Reactive.Banana.Combinators.Extras
import Reactive.Banana.Frameworks as R
import Reactive.Banana.IO as R

import Safe

import Text.Printf.TH

import           Test.QuickCheck as QC hiding ((===),(.||.),(.&&.))
import qualified Test.QuickCheck as QC 
import Test.QuickCheck.Function
import           Test.QuickCheck.Monadic hiding (assert)
import qualified Test.QuickCheck.Monadic as QC
import Test.QuickCheck.Report

import Text.Show.With

data Checker :: (* -> *) -> * where
    Checker :: Checker Proxy
    Monitor :: Checker Identity

-- data Checker m f = Checker 
    -- (forall prop. (IsAssertion prop) => Event prop -> m (f (Event prop)))
    -- (forall prop. (IsAssertion prop) => Behavior prop -> m (f (Behavior prop)))

type Pred a  = a -> Bool
type Check f a prop = forall m g. MonadMomentIO m => ReaderT (Behavior a,Checker g) m (g (f prop))

checkEvent :: (IsAssertion prop,MonadMomentIO m) 
           => Checker f
           -> Event prop -> m (f (Event prop))
checkEvent Checker e = liftMomentIO $ Proxy <$ reactimate (check <$> e) 
    where check prop = checkAssertM prop ""
checkEvent Monitor e = return $ Identity e

checkFutureEvent :: (IsAssertion prop,MonadMomentIO m) 
           => Checker f
           -> Event (Future prop) -> m (f (Event prop))
checkFutureEvent Checker e = liftMomentIO $ Proxy <$ reactimate' (fmap check <$> e) 
    where check prop = checkAssertM prop ""
checkFutureEvent Monitor e = Identity <$> fromFuture e

checkBehavior :: (IsAssertion prop,MonadMomentIO m) 
              => Checker f
              -> Behavior prop -> m (f (Behavior prop))
checkBehavior Checker b = liftMomentIO $ Proxy <$ reactimateB (check <$> b) 
    where check prop = checkAssertM prop ""
checkBehavior Monitor b = return $ Identity b

-- checkAllAsserts :: MonadMomentIO m => Checker m Proxy
-- checkAllAsserts = Checker $ \v e -> do
--     let check prop = checkAssertM prop ""
--     liftMomentIO $ do
--         liftIOLater $ maybe (return ()) check v
--         Proxy <$ reactimate (check <$> e) 

-- readAllAsserts :: Monad m => Checker m Discrete
-- readAllAsserts = Checker $ \v -> return . stepperD v . fmap Just
--         -- (e',h) <- newEvent
--         -- reactimate' $ fmap h <$> e

watchSpec :: MonadMomentIO m
          => Behavior a
          -> ReaderT (Behavior a,Checker Identity) m (Identity k)
          -> m k
watchSpec b cmd = runIdentity <$> runReaderT cmd (b,Monitor)

specify :: MonadMomentIO m
        => Behavior a
        -> ReaderT (Behavior a,Checker Proxy) m k
        -> m k
specify b cmd = runReaderT cmd (b,Checker)

always :: (MonadMomentIO m,IsAssertion a,Pre)
       => Behavior a
       -> m ()
always inv = reactimateB $ (\p -> checkAssertM p "always") <$> inv

invariant' :: (IsAssertion prop,Pre)
           => (a -> prop)
           -> Check Behavior a prop
invariant' p = ReaderT $ \(b,check) -> do
        -- liftMomentIO $ liftIOLater $ checkAssertM (p v) "init value"
        checkBehavior check (p <$> b)

co' :: Pred a
    -> Pred a
    -> Check Event a Bool
co' p q = co $ \s s' -> not (p s) || q s'

not' :: Pred a -> Pred a
not' = fmap not

(.||.) :: Pred a -> Pred a -> Pred a
(.||.) = liftA2 (||)

(.&&.) :: Pred a -> Pred a -> Pred a
(.&&.) = liftA2 (&&)

(.=>.) :: Pred a -> Pred a -> Pred a
(.=>.) p q = not' p .||. q

co :: (IsAssertion prop,Pre)
   => (a -> a -> prop)
   -> Check Event a prop
co r = coE r never

coE :: (IsAssertion prop,Pre)
    => (a -> a -> prop)
    -> Event b
    -> Check Event a prop
coE r e = ReaderT $ \(b,checker) -> do
        dB <- liftMomentIO $ changes b
        let b' = unionWith const 
                        (fmap (flip r) <$> dB)
                        (pure (const (fromBool True)) <$ e)
        checkFutureEvent checker
            $ (liftA2 (flip ($)) <$> (pure <$> b) <@> b') 
            -- & mapped.mapped %~ (\p -> checkAssertM p "coE")

unlessB :: Pred a
        -> Pred a
        -> Check Event a Bool
unlessB p q = co' (p .&&. not' q) (p .||. q)

isoB :: (s -> a) -> (b -> t)
     -> Iso (Behavior s) (Behavior t) (Behavior a) (Behavior b)
isoB f g = iso (fmap f) (fmap g)

unlessE :: Pred a
        -> Event b
        -> Check Event a Bool
unlessE p e = coE (\s s' -> not (p s) || p s') e

constant :: (Eq b,Show b) 
         => (a -> b) 
         -> Check Event a Invariant
constant f = co $ \s s' -> f s === f s'

constantUnlessB :: (Show a,Eq b)
                => (a -> b)
                -> Pred a
                -> Check Event a Invariant
constantUnlessB f p = co $ \s s' -> 
        withPrefix ([printf|s: %s\n|] $ show s)
            $ withPrefix ([printf|s': %s\n|] $ show s')
            $ toInvariant $ p s || f s == f s' || p s'
    where

constantUnlessE :: (Eq b,Show b)
                => (a -> b)
                -> Event k
                -> Check Event a Invariant
constantUnlessE f e = coE (\s s' -> f s === f s') e

togetherOnly :: Event a -> Event b
             -> Check Event k Invariant
togetherOnly e0 e1 = do
    check <- asks snd
    let assert :: These a b -> Invariant
        assert (These _ _) = return ()
        assert (This _)    = "left happening alone" ## False
        assert (That _)    = "right happening alone" ## False
    checkEvent check $ assert <$> eventPair' e0 e1

fails' :: IO a -> IO (Maybe SomeException)
fails' = fmap leftToMaybe . trying id

fails :: IO a -> IO (Either SomeException a)
fails = trying id

prop_invariant :: Bool -> [Maybe Bool] -> Property
prop_invariant x xs = monadicIO $ do
        b <- run $ fails' $ interpretFrameworks (\e -> do
            b <- stepper x e
            always b
            return never) xs
        QC.assert $ isNothing b == and (x:catMaybes xs)

pairs :: (b -> b -> c) -> [b] -> [c]
pairs f xs = zipWith f xs (drop 1 xs)

markPred :: MonadMomentIO m
         => Pred a 
         -> ReaderT (Behavior a) m (Behavior (Maybe UTCTime))
markPred p = do
    b <- ask
    (b',h) <- liftMomentIO $ newBehavior Nothing
    let f x = do
            when (p x) $ h.Just =<< getCurrentTime
    reactimateB $ f <$> b
    return b'

heldFor :: MonadMomentIO m
        => NominalDiffTime 
        -> Pred a
        -> ReaderT (Behavior a) m (Behavior Bool)
heldFor dT p = do
    m <- markPred p & mapped.mapped.mapped %~ addUTCTime dT
    t <- liftMomentIO $ fromPoll getCurrentTime
    return $ liftA2 (maybe (const False) (<=)) m t

prop_co :: Int -> [Maybe Int] -> Property
prop_co x xs = monadicIO $ do
        b <- run $ fails' $ interpretFrameworks (\e -> do
            b <- stepper x e
            specify b $ do
                co (<=)
            return never) xs
        QC.assert $ isNothing b == and (pairs (<=) $ x:catMaybes xs)

prop_unlessB :: Fun Int Bool -> Fun Int Bool
             -> Int -> [Maybe Int] -> Property
prop_unlessB p q x xs = monadicIO $ do
        let isSuffix xs = not (all p' $ take 1 xs) || all p' (takeWhile (not . q') xs)
            p' = apply p
            q' = apply q
        b <- run $ fails' $ interpretFrameworks (\e -> do
            b <- stepper x e
            specify b $ do
                p' `unlessB` q'
            return never) xs
        QC.assert $ isNothing b == all isSuffix (tails $ x:catMaybes xs)

split' :: Event (Maybe a,Maybe b) -> (Event a,Event b)
split' = filterJust.fmap fst &&& filterJust.fmap snd

expandEvtBehPair :: b -> [Maybe (Maybe e, Maybe b)] -> [(Maybe e, b)]
expandEvtBehPair x xs = var'
    where
        var  = scanl f (Nothing,x) xs
        f (_,x) = maybe (Nothing,x) (_2 %~ fromMaybe x)
        var' = concatMap g var & partsOf (traverse._1) %~ (\xs -> drop 1 xs ++ [Nothing])
        g (x,y) = [(x,y),(Nothing,y)]

prop_unlessE :: Bool -> [Maybe (Maybe (),Maybe Bool)] -> Property
prop_unlessE x xs = monadicIO $ do
        let isSuffix xs = not (all snd $ take 1 xs) || all snd (takeWhile (isNothing.fst) $ drop 1 xs)
        b <- run $ fails' $ interpretFrameworks (\e -> do
            let (e',upd) = split' e
            b <- stepper x upd
            specify b $ do
                id `unlessE` e'
            return never) xs
        let var' = expandEvtBehPair x xs
        monitor (counterexample $ show b)
        monitor (counterexample $ show var')
        monitor (counterexample $ show $ filter (not.isSuffix) (tails var'))
        stop $ isNothing b QC.=== all isSuffix (tails var')

prop_constant :: Fun Int Int
              -> Int -> [Maybe Int]
              -> Property
prop_constant f' x xs = monadicIO $ do
        let f = apply f'
        b <- run $ fails' $ interpretFrameworks (\e -> do
            b <- stepper x e
            specify b $ do
                constant f
            return never) xs
        QC.assert $ isNothing b == isConstant f (x:catMaybes xs)

prop_constantUnlessB :: Fun Int Int
                     -> Fun Int Bool
                     -> Int -> [Maybe Int]
                     -> Property
prop_constantUnlessB f' p' x xs = monadicIO $ do
        let f = apply f'
            p = apply p'
        b <- run $ fails' $ interpretFrameworks (\e -> do
            b <- stepper x e
            specify b $ do
                constantUnlessB f p
            return never) xs
        monitor (counterexample $ show b)
        QC.assert $ isNothing b == all (isConstant f . takeWhile (not . p)) 
                                       (tails $ x:catMaybes xs)

shiftRL :: a -> b -> [(a,b)] -> [(a,b)]
shiftRL a b = unzipped %~ (_1 %~ (a:)) . (_2 %~ (\xs -> xs ++ repeat (fromMaybe b $ lastMay xs)))

mkFun :: Eq a => [(a, b)] -> b -> Fun a b
mkFun xs x = Fun undefined' (fromMaybe x . flip L.lookup xs)

takeWhile1 :: (a -> Bool) -> [a] -> [a]
takeWhile1 _ [] = []
takeWhile1 p (x:xs) = x:takeWhile p xs

-- prop_constantUnlessE :: Fun Int Int
--                      -> Int -> [Maybe (Maybe (),Maybe Int)] 
--                      -> Property
-- prop_constantUnlessE f' x xs = monadicIO $ do
--         let isSuffix xs = isConstant f $ takeUntilE xs
--             takeUntilE xs = map snd (takeWhile1 (isNothing.fst) xs)
--             shift xs = shiftRL Nothing x xs
--             f = apply f'
--         (inp,outp) <- run $ interpretFrameworks' (\e -> do
--             let (e',upd) = split' e
--             b <- stepper x upd
--             watchSpec b $ do
--                 f `constantUnlessE` e') xs
--         let var' = expandEvtBehPair x xs
--         -- monitor (counterexample $ [printf|b: %s\n|] $ show b)
--         monitor (counterexample $ [printf|var': %s\n|] $ show var')
--         monitor (counterexample $ [printf|suffix': \n%s\n|] 
--             $ L.unlines $ map (show . takeUntilE) $ tails var')
--         monitor (counterexample $ [printf|shift': \n%s\n|] 
--             $ L.unlines $ map (show . shift) $ tails var')
--         stop $ isNothing _ QC.=== all isSuffix (tails var')

isConstant :: Eq b => (a -> b) -> [a] -> Bool
isConstant f xs = null (drop 1 $ groupBy ((==) `on` f) xs)

type Program m a b = Event a -> m (Event b)
type Spec m a b    = [EventList m a] -> [Maybe b] -> Property
type Claim m a b   = State (Program m a b,Spec m a b)

satisfies :: ( Show (EventList m a)
             , Show a,Show b
             , Frameworks m)
          => Claim m a b k
          -> InitF m
          -> [EventList m a]
          -> Property
satisfies = satisfiesWith showItem showItem

showItem :: Show k => [k] -> [[String]]
showItem = pure . map show

satisfiesWith :: ( Frameworks m)
              => ([EventList m a] -> [[String]])
              -> ([Maybe b] -> [[String]])
              -> Claim m a b k
              -> InitF m
              -> [EventList m a]
              -> Property
satisfiesWith showA showB st = uncurry 
        (satisfiesWith' showA showB) 
        (execState st (defP,defS))
    where
      defP _ = return never
      defS _ _ = QC.property False

selectM :: Proxy m -> Claim m a b ()
selectM Proxy = return ()

selectA :: Proxy a -> Claim m a b ()
selectA Proxy = return ()

selectB :: Proxy b -> Claim m a b ()
selectB Proxy = return ()

newtype ParamA' (m :: * -> *) a b = ParamA (a -> b)
type ParamA m a = ParamA' m ((),()) a

program :: Program m a b
        -> Claim m a b ()
program p = _1 .= p

specification :: (Frameworks m,Testable prop)
              => ([EventList m a] -> [Maybe b] -> prop)
              -> Claim m a b ()
specification p = _2 .= (p & mapped.mapped %~ QC.property)

satisfies' :: ( Testable prop
              , Show (EventList m a)
              , Show a,Show b
              , Frameworks m)
           => (Event a -> m (Event b))
           -> ([EventList m a] -> [Maybe b] -> prop)
           -> InitF m
           -> [EventList m a]
           -> Property
satisfies' = satisfiesWith' showItem showItem

satisfiesWith' :: (Testable prop
                  -- , Show (EventList m a)
                  -- , Show a,Show b
                  , Frameworks m)
               => ([EventList m a] -> [[String]])
               -> ([Maybe b] -> [[String]])
               -> (Event a -> m (Event b))
               -> ([EventList m a] -> [Maybe b] -> prop)
               -> InitF m
               -> [EventList m a]
               -> Property
satisfiesWith' showA showB f spec init input = monadicIO $ do
        (xs,ys) <- run $ interpret' f init input
        monitor (counterexample $ prependIndent "input:  " $ L.unlines $ map (showWith id) (showA xs))
        monitor (counterexample $ prependIndent "output: " $ L.unlines $ map (showWith id) (showB ys))
        stop (spec xs ys)

return []

run_tests :: (PropName -> Property -> IO (a, Result))
          -> IO ([a], Bool)
run_tests = $forAllProperties'
