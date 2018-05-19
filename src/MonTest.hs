{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module CarrierTest where


import Data.Profunctor
import Data.Profunctor.Composition
import Data.Profunctor.Strong

import Control.Monad ((>=>))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

-- This is isomorphic to Pastro (Exchange a a)
data Carrier a x y where
  Carrier :: (x -> (a, z)) -> ((a, z) -> y) -> Carrier a x y

comult :: Carrier a x y -> Procompose (Carrier a) (Carrier a) x y
comult (Carrier f g)
  = Procompose (Carrier id g) (Carrier f id)

counit :: Carrier a x y -> (x -> y)
counit (Carrier f g) = g . f

type Lens' s a = forall x y. Carrier s x y -> Carrier a x y

get :: Lens' s a -> s -> a
get l = case l (Carrier (\s -> (s, ())) (const ())) of
          Carrier f g -> fst . f

put :: Lens' s a -> s -> a -> s
put l s a = case l (Carrier (\s -> (s, ())) fst) of
              Carrier f g -> g $ (\(_, z) -> (a, z)) $ (f s)

_1 :: Lens' (a, b) a
_1 (Carrier f g) = Carrier (assoc . f) (g . unassoc)
  where assoc   ((x, y), z) = (x, (y, z))
        unassoc (x, (y, z)) = ((x, y), z)

-- TODO: This might require a Kleisli strength on m so that we have a
-- well behaved "preproduct" on the Kleisli category

data MCarrier m a x y where
  MCarrier :: (x -> m (a, z)) -> ((a, z) -> m y) -> MCarrier m a x y

type MLens' m s a = forall x y. MCarrier m s x y -> MCarrier m a x y

mget :: Monad m => MLens' m s a -> s -> m a
mget l = case l (MCarrier (\s -> return (s, ())) (const $ return ())) of
          MCarrier f g -> fmap fst . f

mput :: Monad m => MLens' m s a -> s -> a -> m s
mput l s a = case l (MCarrier (\s -> return (s, ())) (return . fst)) of
              MCarrier f g -> do
                (_, z) <- f s
                g (a, z)

-- _1 :: Lens' (a, b) a
-- _1 (Carrier f g) = Carrier (assoc . f) (g . unassoc)
--   where assoc   ((x, y), z) = (x, (y, z))
--         unassoc (x, (y, z)) = ((x, y), z)


class KleisliStrong m where
  kstrong :: m a -> m b -> m (a, b)

instance KleisliStrong (State a)
instance KleisliStrong (Reader a)
instance (Monoid m) => KleisliStrong (Writer m) -- Commutative only

class MProfunctor m p where
  mdimap :: (a -> m b) -> (c -> m d) -> p b c -> p a d

instance (Monad m) => MProfunctor m (Star m) where
  mdimap f g (Star p) = Star (f >=> p >=> g)


data SymCarrier a x y where
  SymCarrier :: ((x, z) -> (a, z)) -> ((a, z) -> (y, z)) -> SymCarrier a x y
