{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Stateful where

import Control.Monad (liftM, ap, (>=>))

data State q a = State { runState :: q -> (a, q) }

getState :: State q q
getState = State $ \q -> (q, q)

putState :: q -> State q ()
putState q = State $ \_ -> ((), q)

secretly :: State q a -> State q a
secretly act = do
  q <- getState
  a <- act
  putState q
  return a

instance Functor (State q) where
  fmap = liftM

instance Applicative (State q) where
  pure = return
  (<*>) = ap

instance Monad (State q) where
  return a = State (\q -> (a, q))
  act >>= k = State $ \st ->
                        let (x, st') = runState act st
                        in runState (k x) st'

data Stateful q s a where
  Stateful :: (s -> State q (m, a)) -> ((m, a) -> State q s) -> Stateful q s a

data Concrete q s a where
  Concrete :: (s -> State q a) -> (s -> q -> a -> State q s) -> Concrete q s a

to :: Stateful q s a -> Concrete q s a
to (Stateful l r) = Concrete mget mput
  where mget = fmap snd . l
        mput s q a = let ((m, _), _) = runState (l s) q
                     in r (m, a)

fro :: forall q s a. Concrete q s a -> Stateful q s a
fro (Concrete mget mput) = Stateful l r
  where l :: s -> State q ((s, q), a)
        l s = do
          q <- getState
          a <- mget s
          return ((s, q), a)
        -- l s = State $ \q -> let (a, q') = (runState $ mget s) q
        --                     in (((s, q), a), q')
        r :: ((s, q), a) -> State q s
        r ((s, q), a) = mput s q a

data Twice q s a where
  Twice :: (s -> State q (m, a)) -> ((m, a) -> State q (n, a)) -> ((n, a) -> State q s) -> Twice q s a

data ConcreteTwice q s a where
  ConcreteTwice :: (s -> State q a) -> (s -> q -> a -> State q a) -> (s -> q -> a -> q -> a -> State q s) -> ConcreteTwice q s a

toTwice :: forall q s a. Twice q s a -> ConcreteTwice q s a
toTwice (Twice l c r) = ConcreteTwice x y z
  where x :: s -> State q a
        x = fmap snd . l
        y :: s -> q -> a -> State q a
        y s q a = let ((m, _), _) = runState (l s) q
                  in fmap snd $ c (m, a)
        z :: s -> q -> a -> q -> a -> State q s
        z s q1 a1 q2 a2 =
          let ((m, _), _) = runState (l s) q1
              ((n, _), _) = runState (c (m, a1)) q2
          in r (n, a2)

mget = undefined
mput = undefined

l s = do
  q <- getState
  a <- mget s
  return ((s, q), a)

r ((s, q), a) = mput s q a

-- outside = l >=> r
-- outside = \x -> l x >>= r
outside s = do
  q <- getState
  a <- mget s
  mput s q a

-- once = toTwice (Twice l return r)
once = ConcreteTwice x y z
  where x :: s -> State q a
        x s = mget s
        y :: s -> q -> a -> State q a
        y s q a = return a
        z :: s -> q -> a -> q -> a -> State q s
        z s q1 a1 q2 a2 = mput s q1 a2

-- c = r >=> l
-- c (m, a) = r (m, a) >>= l
-- c ((s, q), a) = mput s q a >>= l
c ((s, q), a) = do
  s' <- mput s q a
  q' <- getState
  a' <- mget s'
  return ((s', q'), a')

-- twice = toTwice (Twice l (r >=> l) r)
twice = ConcreteTwice x y z
  where x :: s -> State q a
        x s = mget s
        y :: s -> q -> a -> State q a
        y s q a = do s' <- mput s q a
                     mget s'
        z :: s -> q -> a -> q -> a -> State q s
        z s q1 a1 q2 a2 =
          let (s'', q'') = runState (mput s q1 a1) q2
          in mput s'' q'' a2
