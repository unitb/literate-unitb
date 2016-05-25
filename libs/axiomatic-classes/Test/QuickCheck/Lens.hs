{-# LANGUAGE TemplateHaskell #-}
module Test.QuickCheck.Lens where

import Control.Lens

import Test.QuickCheck
import Test.QuickCheck.Exception
import Test.QuickCheck.Random

makePrisms ''Result

pairs :: Iso (s0,s1,s2,s3,s4,s5,s6,s7,s8,s9) 
             (t0,t1,t2,t3,t4,t5,t6,t7,t8,t9) 
             ((s0,s1,s2,s3,s4),(s5,s6,s7,s8,s9)) 
             ((t0,t1,t2,t3,t4),(t5,t6,t7,t8,t9)) 
pairs = iso (\(s0,s1,s2,s3,s4,s5,s6,s7,s8,s9) -> ((s0,s1,s2,s3,s4),(s5,s6,s7,s8,s9)))
            (\((s0,s1,s2,s3,s4),(s5,s6,s7,s8,s9)) -> (s0,s1,s2,s3,s4,s5,s6,s7,s8,s9))

argReplay :: Lens' Args (Maybe (QCGen, Int))
argReplay f x = (\r' -> x { replay = r' }) <$> f (replay x)

argMaxSuccess :: Lens' Args Int
argMaxSuccess f x = (\r' -> x { maxSuccess = r' }) <$> f (maxSuccess x)

argMaxDiscardRatio :: Lens' Args Int
argMaxDiscardRatio f x = (\r' -> x { maxDiscardRatio = r' }) <$> f (maxDiscardRatio x)

argMaxSize :: Lens' Args Int
argMaxSize f x = (\r' -> x { maxSize = r' }) <$> f (maxSize x)

argChatty :: Lens' Args Bool
argChatty f x = (\r' -> x { chatty = r' }) <$> f (chatty x)

type Failure = (Int,
                 Int,
                 Int,
                 Int,
                 QCGen,
                 Int,
                 String,
                 Maybe AnException,
                 [(String, Int)],
                 String)

resNumTests :: Lens' Result Int
resNumTests f x = (\r' -> x { numTests = r' }) <$> f (numTests x)

resLabels :: Lens' Result [(String,Int)]
resLabels f x = (\r' -> x { labels = r' }) <$> f (labels x)

resOutput :: Lens' Result String
resOutput f x = (\r' -> x { output = r' }) <$> f (output x)

resNumShrinks :: Lens' Failure Int
resNumShrinks = pairs . _1 . _2

resNumShrinkTries :: Lens' Failure Int
resNumShrinkTries = pairs . _1 . _3

resNumShrinkFinal :: Lens' Failure Int
resNumShrinkFinal = pairs . _1 . _4

resUsedSeed :: Lens' Failure QCGen
resUsedSeed = pairs . _1 . _5

resUsedSize :: Lens' Failure Int
resUsedSize = pairs . _2 . _1

resReason :: Lens' Failure String
resReason = pairs . _2 . _2

resTheException :: Lens' Failure (Maybe AnException)
resTheException = pairs . _2 . _3

