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
        [ QuickCheckProps "QuickCheck : Reactive.Banana.Property" Prop.run_tests
        -- , aCase _ KB.run_tests _ 
        , QuickCheckProps "QuickCheck : Reactive.Banana.FileSystem" FS.run_tests
        , QuickCheckProps "QuickCheck : Reactive.Banana.Async2" Async.run_tests ]
