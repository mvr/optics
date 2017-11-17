module BadPrism where

import Control.Lens

data MissCounter a = Misses Int a deriving (Show)

bad :: Eq a => Prism' (MissCounter a) a
bad = prism review matching
  where review = Misses 0
        matching (Misses 0 a) = Right a
        matching (Misses n a) = Left (Misses (n + 1) a)
