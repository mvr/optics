{-# LANGUAGE FlexibleInstances #-}
module Comonoidal where

import Control.Comonad
import Data.Profunctor
import Data.Profunctor.Composition

class Comonoidal p where
  comult :: p a b -> Procompose p p a b
  counit :: p a b -> (a -> b)


data Exchange a b s t = Exchange (s -> a) (b -> t)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange l r) = Exchange (l . f) (g . r)

instance Comonoidal (Exchange x x) where
  comult (Exchange l r) = Procompose (Exchange id r) (Exchange l id)
  counit (Exchange l r) = r . l

instance Comonad m => Comonoidal (Star m) where
  comult (Star f) = Procompose (Star f) (Star _)
  counit (Star f) = extract . f
