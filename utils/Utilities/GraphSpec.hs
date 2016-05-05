module Utilities.GraphSpec where

    -- Module
import qualified Utilities.Graph as G hiding (map)

    -- Libraries
import Test.QuickCheck

axm_def :: (Show a, Arbitrary a, Ord a, G.Composition b) 
         => G.Matrix a b -> Property
axm_def m' = forAll arbitrary $ \(x,z) -> 
        m (x,z)  ==  G.uppest (map (\y -> m(x,y) `seq` m(y,z)) $ G.vertices m')
    where
        m = (m' G.!)

-- prop_def :: Property
-- prop_def = (forAll arbitrary (axm_def :: G.Matrix Int Bool -> Property))
--             .&&. (forAll arbitrary (axm_def :: G.Matrix Int (G.Min Int) -> Property))

return []
run_spec :: IO Bool
run_spec = $forAllProperties (quickCheckWithResult stdArgs { chatty = False })
