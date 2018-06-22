{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Monadic where

import Control.Monad (liftM, ap, (>=>))

data Monadic t s a where
  Monadic :: (s -> t (m, a)) -> ((m, a) -> t s) -> Monadic t s a

data Concrete t s a where
  Concrete :: (s -> t (a -> t s, a)) -> Concrete t s a

to :: Monad t => Monadic t s a -> Concrete t s a
to (Monadic l r) = Concrete $ \s -> do
  (m, a) <- l s
  let f a' = r (m, a')
  return (f, a)

fro :: Monad t => Concrete t s a -> Monadic t s a
fro (Concrete f) = Monadic f (\(i, a) -> i a)

data Twice t s a where
  Twice :: (s -> t (m, a)) -> ((m, a) -> t (n, a)) -> ((n, a) -> t s) -> Twice t s a

-- data ConcreteTwice q s a where
--   ConcreteTwice ::
