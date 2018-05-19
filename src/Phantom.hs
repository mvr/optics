{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module Phantom where

import Control.Applicative
import Data.Functor.Identity
import Data.Profunctor
import Data.Coerce

class Functor f => Pointed f where
  point :: a -> f a

instance Pointed (Either a) where point = Right

class Functor f => Copointed f where
  copoint :: f a -> a

instance Copointed ((,) a) where copoint = snd
instance Copointed Identity where copoint = runIdentity

class Profunctor p => StrongPointed p where
  enpointen :: Pointed f => p a b -> p (f a) (f b)

instance StrongPointed (->) where
  enpointen = fmap

class Profunctor p => StrongCopointed p where
  encopointen :: Copointed f => p a b -> p (f a) (f b)

instance StrongCopointed (->) where
  encopointen = fmap

--------------------------------------------------------------------------------

data Getter r a b = Getter { runGetter :: a -> Const r b }

instance Profunctor (Getter r) where
  dimap f g (Getter p) = Getter $ fmap g . p . f

instance StrongCopointed (Getter r) where
  encopointen (Getter p) = Getter $ coerce . p . copoint

(^.) :: s -> (Getter a a a -> Getter a s s) -> a
s ^. l = getConst $ runGetter (l (Getter Const)) s

--------------------------------------------------------------------------------

data Direct s a where
  Direct :: Copointed f => (s -> f a) -> (f a -> s) -> Direct s a

toDirect :: (s -> a) -> (s -> s) -> Direct s a
toDirect f g = Direct (\s -> (g s, f s)) fst

fromDirect :: Direct s a -> (s -> a, s -> s)
fromDirect (Direct l r) = (copoint . l, r . l)

-- toDirect $ fromDirect (Direct l r)
-- toDirect (copoint . l, r . l)
-- Direct (\s -> ((r . l) s, (copoint . l) s)) fst
-- Direct (\p -> (p, copoint p)) . l) (r . fst)
-- ...

-- fromDirect $ toDirect f g
-- fromDirect $ Direct (\s -> (g s, f s)) fst
-- (copoint . (\s -> (g s, f s)), g)
-- (f, g)

rt (Direct l r) = Direct (\s -> (s, copoint (l s))) fst

to :: (s -> a) -> (forall p. StrongCopointed p => p a a -> p s s)
to l = dimap diag fst . encopointen . lmap l
  where diag s = (s, s)

unto :: (a -> s) -> (forall p. StrongPointed p => p a a -> p s s)
unto l = dimap Left codiag . enpointen . rmap l
  where codiag (Left a) = a
        codiag (Right a) = a
