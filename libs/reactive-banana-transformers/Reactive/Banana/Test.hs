module Reactive.Banana.Test where

import Reactive.Banana.Async as Async
import Reactive.Banana.FileSystem as FS
import Reactive.Banana.Keyboard as KB ()
import Reactive.Banana.Property as Prop

import Test.UnitTest

test_case :: TestCase
test_case = test

test :: TestCase
test = test_cases
        "Reactive.Banana extensions"
        [ Case "QuickCheck : Reactive.Banana.Property" Prop.run_tests True
        -- , Case _ KB.run_tests _ 
        , Case "QuickCheck : Reactive.Banana.FileSystem" FS.run_tests True
        , Case "QuickCheck : Reactive.Banana.Async2" Async.run_tests True ]
