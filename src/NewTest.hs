{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
--{-# LANGUAGE DeriveTraversable #-}
--{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module NewTest where

import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor
import Data.Void
import GHC.Exts (Constraint)

class (c Identity) => Action (c :: (* -> *) -> Constraint) where
  type Wanderer c (a :: *) (b :: *) = (p :: * -> * -> *) | p -> c a b
  type Wanderer c a b = LoneWanderer c a b

  composeDict :: Dict (c f) ->
                 Dict (c g) ->
                 Dict (c (Compose f g))

  functorialDict :: c f => Dict (Functor f)

  -- TODO: make these isos!
  stray :: Wanderer c a b x y -> LoneWanderer c a b x y
  default stray :: LoneWanderer c a b x y -> LoneWanderer c a b x y
  stray = id

  unstray :: LoneWanderer c a b x y -> Wanderer c a b x y
  default unstray :: LoneWanderer c a b x y -> LoneWanderer c a b x y
  unstray = id

class (Action c, Profunctor p) => Tambara c p where
  walk :: c f => p a b -> p (f a) (f b)
  walk = persuade @c (unstray $ walk @c sell)

  persuade :: (Wanderer c a b) s t -> (p a b -> p s t)

--------------------------------------------------------------------------------
-- Exchange, Pastro
--------------------------------------------------------------------------------

data Exchange a b s t = Exchange (s -> a) (b -> t)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange l r) = Exchange (l . f) (g . r)

data Pastro (c :: (* -> *) -> Constraint) p a b where
  Pastro :: c f => (a -> f x) -> p x y -> (f y -> b) ->  Pastro c p a b

instance Profunctor (Pastro c p) where
  dimap f g (Pastro l m r) = Pastro (l . f) m (g . r)

data LoneWanderer c a b x y = LoneWanderer (Pastro c (Exchange a b) x y)

instance Profunctor (LoneWanderer c a b) where
  dimap f g (LoneWanderer p) = LoneWanderer (dimap f g p)

sell :: (Action c) => LoneWanderer c a b a b
sell = LoneWanderer (Pastro Identity (Exchange id id) runIdentity)

lonePersuade :: forall c p s t a b. (Action c, Tambara c p) => (LoneWanderer c a b) s t -> (p a b -> p s t)
lonePersuade (LoneWanderer (Pastro (l :: x -> f x') (Exchange l' r') (r :: f y' -> y))) p
  = dimap _ _ (walk @c @p @f p)

instance (Action c) => Tambara c (LoneWanderer c a b) where
  walk :: forall c f a b x y. (Action c, c f) => LoneWanderer c a b x y -> LoneWanderer c a b (f x) (f y)
  walk (LoneWanderer (Pastro (l :: x -> g x') p (r :: g y' -> y)))
    = case functorialDict @c @f of
        Dict -> case composeDict @c @f @g Dict Dict of
          Dict -> LoneWanderer (Pastro (Compose . fmap l) p (fmap r . getCompose))

  persuade = undefined

--------------------------------------------------------------------------------
-- Actions
--------------------------------------------------------------------------------

------------------------------
-- Trivial

class Functor f => IsIdentity f where
  toIdentity :: a -> f a
  fromIdentity :: f a -> a

instance IsIdentity Identity where
  toIdentity   = Identity
  fromIdentity = runIdentity

instance (IsIdentity f, IsIdentity g) => IsIdentity (Compose f g) where
  toIdentity a = Compose (toIdentity (toIdentity a))
  fromIdentity (Compose fga) = fromIdentity (fromIdentity fga)

instance Action IsIdentity where
  type Wanderer IsIdentity a b = Exchange a b
  composeDict Dict Dict = Dict
  functorialDict = Dict

  stray e = LoneWanderer (Pastro Identity e runIdentity)
  unstray (LoneWanderer (Pastro l p r)) = dimap (fromIdentity . l) (r . toIdentity) p



------------------------------
-- Product

class Functor f => IsProduct f where
  type Complement f
  -- TODO: make these iso
  toPair :: f a -> (Complement f, a)
  fromPair :: (Complement f, a) -> f a

instance IsProduct ((,) e) where
  type Complement ((,) e) = e
  toPair = id
  fromPair = id

instance IsProduct Identity where
  type Complement Identity = ()
  toPair (Identity a) = ((), a)
  fromPair ((), a) = Identity a

instance (IsProduct f, IsProduct g) => IsProduct (Compose f g) where
  type Complement (Compose f g) = (Complement f, Complement g)
  toPair = undefined
  fromPair = undefined

data Context a b x = Context (b -> x) a

instance Action IsProduct where
  type Wanderer IsProduct a b = Star (Context a b)
  composeDict Dict Dict = Dict
  functorialDict = Dict

  stray = undefined
  unstray = undefined

instance (Functor f) => Tambara IsProduct (Star f) where
  walk (Star f) = Star $ \p -> let (c, a) = toPair p in
                               fromPair <$> (c,) <$> f a

------------------------------
-- Sum

class Functor f => IsSum f where
  type Summand f
  -- TODO: make these iso
  toSum :: f a -> Either (Summand f) a
  fromSum :: Either (Summand f) a -> f a

instance IsSum (Either a) where
  type Summand (Either a) = a
  toSum = id
  fromSum = id

instance IsSum Identity where
  type Summand Identity = Void
  toSum (Identity a) = Right a
  fromSum (Left v) = absurd v
  fromSum (Right a) = Identity a

------------------------------
-- Todo

class Pointed f where
class Copointed f where

--------------------------------------------------------------------------------
-- Optics
--------------------------------------------------------------------------------

type Optical p s t a b = p a b -> p s t
type Optic c s t a b = forall p. (Tambara c p) => Optical p s t a b

type Iso        s t a b = Optic IsIdentity  s t a b
type Lens       s t a b = Optic IsProduct   s t a b
type Prism      s t a b = Optic IsSum       s t a b
type Traversal  s t a b = Optic Traversable s t a b
type Setter     s t a b = Optic Functor     s t a b
type Getter     s t a b = Optic Copointed   s t a b
type Review     s t a b = Optic Pointed     s t a b
type Fold       s t a b = Optic Foldable    s t a b

_2 :: Lens (c, a) (c, b) a b
_2 = walk @IsProduct

--------------------------------------------------------------------------------
-- Notes
--------------------------------------------------------------------------------

-- The typeclasses IsIdentity, IsProduct and IsSum could all be something like
-- IsoToIdentitiy, IsoToProdut and IsoToSum
-- This would require wrapping/unwrapping everywhere

-- LoneWanderer could be Yoneda-reduced to
-- data LoneWanderer c a b x y where
--   LoneWanderer :: c f => (f b -> y) -> (x -> f a) -> LoneWanderer c a b x y
