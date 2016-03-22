module Utilities.GraphSpec where

    -- Module
import qualified Utilities.Graph as G hiding (map)

    -- Libraries
import Test.QuickCheck

instance (Ord a,Enum a,Eq b,Arbitrary b) => Arbitrary (G.Matrix a b) where
    arbitrary = do
        (Positive m) <- arbitrary
        -- (Positive n) <- arbitrary
        -- let xs = map toEnum [1..m]
        def <- arbitrary
        ys  <- listOf $ do
            i <- choose (1,m)
            j <- choose (1,m)
            x <- arbitrary
            return ((toEnum i, toEnum j),x)
        return $ G.from_list ys def

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
