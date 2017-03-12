{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module NewTest where

import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Profunctor
import Data.Proxy
import Data.Tagged
import Data.Tuple (swap)
import Data.Type.Bool
import Data.Type.Equality
import Data.Void
import GHC.Exts (Constraint)
import Unsafe.Coerce

--------------------------------------------------------------------------------
-- Overview
--------------------------------------------------------------------------------
-- * Normal optics are specified by an `Action c`, i.e., a subcategory of
--   [Hask, Hask] that is closed under composition
-- * An Optic is completely determined by its behaviour on `Wanderer c a b`
-- * The default, `Pastro (Exchange a b)` always works as the Wanderer,
--   but can be overridden to something more familiar/efficient

-- * The funny optics, Getter, Review, Fold, are specified by an Action
--   that is not functorial: instead we have a subcategory of [ob Hask, Hask]
-- * `Pastro` no longer gives the free "Tambara module", we need
--   something freer: here it is called `Pasture`

-- The Dicts in Action would be constraints on the typeclass if that
-- were possible.

-- TODO:
-- * Replace IsIdentity with Functor + Contravariant. Are there
--   similar tricks for IsProduct and IsSum?

--------------------------------------------------------------------------------
-- Action
--------------------------------------------------------------------------------

class Action (c :: (* -> *) -> Constraint) where
  type Wanderer c (a :: *) (b :: *) = (p :: * -> * -> *) | p -> c a b
  type Wanderer c a b = LoneWanderer c a b

  wandererDict :: Dict (Tambara c (Wanderer c a b))
  default wandererDict :: Dict (Tambara c (LoneWanderer c a b))
  wandererDict = Dict

  -- TODO: make these isos!
  stray :: Wanderer c a b x y -> LoneWanderer c a b x y
  default stray :: LoneWanderer c a b x y -> LoneWanderer c a b x y
  stray = id

  unstray :: LoneWanderer c a b x y -> Wanderer c a b x y
  default unstray :: LoneWanderer c a b x y -> LoneWanderer c a b x y
  unstray = id

class (Action c, c Identity) => FunctorialAction c where
  composeDict :: Dict (c f) ->
                 Dict (c g) ->
                 Dict (c (Compose f g))

  functorialDict :: c f => Dict (Functor f)
  default functorialDict :: (Functor f, c f) => Dict (Functor f)
  functorialDict = Dict

class (Action c, Profunctor p
      ) => Tambara c p where
  {-# MINIMAL walk | persuade #-}
  walk :: c f => p a b -> p (f a) (f b)
  walk = persuade @c (unstray $ walk @c sell)

  persuade :: (Wanderer c a b) s t -> (p a b -> p s t)
  persuade w p = lowerPasture $ insertPasture p lw
    where (LoneWanderer lw) = stray w

instance (FunctorialAction c) => Tambara c (->) where
  walk :: forall f a b. c f => (->) a b -> (->) (f a) (f b)
  walk = case functorialDict @c @f of Dict -> fmap

--------------------------------------------------------------------------------
-- Exchange, Pastro
--------------------------------------------------------------------------------

----------------------------------------
-- Pastro

data Pastro (c :: (* -> *) -> Constraint) p a b where
  Pastro :: c f => (a -> f x) -> p x y -> (f y -> b) -> Pastro c p a b

instance Profunctor (Pastro c p) where
  dimap f g (Pastro l m r) = Pastro (l . f) m (g . r)

instance (FunctorialAction c) => Tambara c (Pastro c p) where
  walk :: forall f a b. c f => Pastro c p a b -> Pastro c p (f a) (f b)
  walk (Pastro (l :: a -> g x) p (r :: g y -> b))
    = case functorialDict @c @f of
        Dict -> case composeDict @c @f @g Dict Dict of
          Dict -> Pastro (Compose . fmap l) p (fmap r . getCompose)

liftPastro :: (c Identity) => p a b -> Pastro c p a b
liftPastro p = Pastro Identity p runIdentity

----------------------------------------
-- Pasture (An even freer Pastro)

data Pasture (c :: (* -> *) -> Constraint) p a b where
  Pure :: p a b -> Pasture c p a b
  Dimap :: (a -> x) -> Pasture c p x y -> (y -> b) -> Pasture c p a b
  Walk :: c f => Pasture c p a b -> Pasture c p (f a) (f b)

instance Profunctor (Pasture c p) where
  dimap f g (Pure p) = Dimap f (Pure p) g
  dimap f g (Dimap l p r) = Dimap (l . f) p (g . r)
  dimap f g (Walk p) = Dimap f (Walk p) g

instance (Action c) => Tambara c (Pasture c p) where
  walk = Walk

liftPasture :: p a b -> Pasture c p a b
liftPasture = Pure

-- NOT assumed to be a functorial action!
lowerPasture :: forall c p a b. (Tambara c p) => Pasture c p a b -> p a b
lowerPasture (Pure p) = p
lowerPasture (Dimap l p r) = dimap l r (lowerPasture p)
lowerPasture (Walk p) = walk @c (lowerPasture p)

hoistPasture :: (forall a b. p a b -> q a b) -> (Pasture c p a b -> Pasture c q a b)
hoistPasture f (Pure p) = Pure (f p)
hoistPasture f (Dimap l p r) = Dimap l (hoistPasture f p) r
hoistPasture f (Walk p) = Walk (hoistPasture f p)

insertPasture :: Profunctor p => p a b -> Pasture c (Exchange a b) s t -> Pasture c p s t
insertPasture p = hoistPasture (\(Exchange l r) -> dimap l r p)

collapsePasture :: (FunctorialAction c) => Pasture c p s t -> Pastro c p s t
collapsePasture = lowerPasture . hoistPasture liftPastro

----------------------------------------
-- Exchange, LoneWanderer

data Exchange a b s t = Exchange (s -> a) (b -> t)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange l r) = Exchange (l . f) (g . r)

instance Tambara IsIdentity (Exchange a b) where
  walk = dimap fromIdentity toIdentity

-- I would prefer this to be a `type`, but I need to partially apply
-- it in `Action`
data LoneWanderer c a b x y = LoneWanderer (Pasture c (Exchange a b) x y)

instance Profunctor (LoneWanderer c a b) where
  dimap f g (LoneWanderer p) = LoneWanderer (dimap f g p)

instance (Action c) => Tambara c (LoneWanderer c a b) where
  walk (LoneWanderer p) = LoneWanderer (walk @c p)

sell :: (Action c) => LoneWanderer c a b a b
sell = LoneWanderer (Pure (Exchange id id))


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
  wandererDict = Dict

  stray p = LoneWanderer (liftPasture p)
  unstray (LoneWanderer p) = lowerPasture p

instance FunctorialAction IsIdentity where
  composeDict Dict Dict = Dict

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
  toPair (Compose fga)
    | (f, ga) <- toPair fga
    , (g, a)  <- toPair ga = ((f, g), a)
  fromPair ((f, g), a) = Compose $ fromPair (f, fromPair (g, a))

data Context a b x = Context a (b -> x) deriving (Functor)

instance Action IsProduct where
  type Wanderer IsProduct a b = Star (Context a b)
  wandererDict = Dict

  stray (Star f) = dimap (\x -> let (Context a _) = f x in (x, a))
                         (\(x, b) -> let (Context _ g) = f x in g b)
                         (walk @IsProduct sell)
  unstray (LoneWanderer p) = lowerPasture $ hoistPasture f p
    where f (Exchange l r) = Star (\s -> Context (l s) r)

instance FunctorialAction IsProduct where
  composeDict Dict Dict = Dict

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
-- Pointed

-- This section is absolutely outrageous
-- The dancing around is needed to defeat parametricity!

class PointFor a f where
  pointfor :: a -> f a

class Pointish f where
  pointishDict :: Dict (PointFor a f)
  default pointishDict :: PointFor a f => Dict (PointFor a f)
  pointishDict = Dict

data Pointer t b a where
  PNormal :: a -> Pointer t b a
  PExtra :: ((a == b) ~ True) => t -> Pointer t b a

putExtra :: t -> Pointer t b b
putExtra = PExtra

instance PointFor a (Pointer t b) where
  pointfor = PNormal

instance Pointish (Pointer t b)

phantom :: Tambara Pointish p => p a b -> p c b
phantom =   dimap (putExtra . Tagged) (unTagged . (\(PNormal a) -> a))
          . walk @Pointish
          . dimap (unTagged :: Tagged True a -> a) (Tagged :: b -> Tagged False b)

data Forgetter a b x y = Forgetter { runForgetter :: (b -> y) }

instance Profunctor (Forgetter a b) where
  dimap f g (Forgetter r) = Forgetter (g . r)

instance Tambara Pointish (Forgetter a b) where
  walk :: forall f a b x y. Pointish f => Forgetter a b x y -> Forgetter a b (f x) (f y)
  walk (Forgetter r) = case pointishDict @f @y of
    Dict -> Forgetter (pointfor . r)

instance Action Pointish where
  type Wanderer Pointish a b = Forgetter a b
  wandererDict = Dict

  stray (Forgetter r) = phantom $ rmap r sell
  unstray (LoneWanderer p) = lowerPasture $ hoistPasture f p
    where f (Exchange l r) = Forgetter r

------------------------------
-- Copointish

class CopointFor a f where
  copointfor :: f a -> a

class Copointish f where
  copointishDict :: Dict (CopointFor a f)
  default copointishDict :: CopointFor a f => Dict (CopointFor a f)
  copointishDict = Dict

eqToRefl :: forall a b. (a == b) ~ 'True => a :~: b
eqToRefl = unsafeCoerce (Refl :: () :~: ())

data Copointer t b a where
  CPNormal :: ((a == b) ~ False) => a -> Copointer t b a
  CPExtra :: ((a == b) ~ True) => t -> b -> Copointer t b a

getExtra :: Copointer t b b -> t
getExtra (CPExtra t b) = t

instance CopointFor a (Copointer t b) where
  copointfor (CPExtra t b) = case eqToRefl :: a :~: b of Refl -> b
  copointfor (CPNormal a) = a

-- Some fiddling is needed so that a and b are unequal
cophantom :: Tambara Copointish p => p a b -> p a c
cophantom =   dimap (CPNormal . Tagged) (unTagged . getExtra)
            . walk @Copointish
            . dimap (unTagged :: Tagged True a -> a) (Tagged :: b -> Tagged False b)

instance Copointish (Copointer t b)

data Coforgetter a b x y = Coforgetter { runCoforgetter :: (x -> a) }

instance Profunctor (Coforgetter a b) where
  dimap f g (Coforgetter l) = Coforgetter (l . f)

instance Tambara Copointish (Coforgetter a b) where
  walk :: forall f a b x y. Copointish f => Coforgetter a b x y -> Coforgetter a b (f x) (f y)
  walk (Coforgetter l) = case copointishDict @f @x of
    Dict -> Coforgetter (l . copointfor)

instance Action Copointish where
  type Wanderer Copointish a b = Coforgetter a b
  wandererDict = Dict

  stray (Coforgetter l) = cophantom $ lmap l sell
  unstray (LoneWanderer p) = lowerPasture $ hoistPasture f p
    where f (Exchange l r) = Coforgetter l

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
type Getter     s t a b = Optic Copointish  s t a b
--type Review     s t a b = Optic Pointish    s t a b
--type Fold       s t a b = Optic Foldable    s t a b

type AnIso       s t a b = Optical (Wanderer IsIdentity  a b) s t a b
type ALens       s t a b = Optical (Wanderer IsProduct   a b) s t a b
type APrism      s t a b = Optical (Wanderer IsSum       a b) s t a b
type ATraversal  s t a b = Optical (Wanderer Traversable a b) s t a b
type ASetter     s t a b = Optical (Wanderer Functor     a b) s t a b
type AGetter     s t a b = Optical (Wanderer Copointish  a b) s t a b
-- type AReview     s t a b = Optical (Wanderer Pointish    a b) s t a b
-- type AFold       s t a b = Optical (Wanderer Foldish     a b) s t a b

_1 :: Lens (a, c) (b, c) a b
_1 = dimap swap swap . walk @IsProduct

_2 :: Lens (c, a) (c, b) a b
_2 = walk @IsProduct

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso sa bt = dimap sa bt

to :: (s -> a) -> Getter s t a b
to f = persuade (Coforgetter f)

from :: Iso s t a b -> Iso b a t s
from i = iso r l
  where (Exchange l r) = i (Exchange id id)

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

view :: AGetter s t a b -> s -> a
view l = runCoforgetter $ l (Coforgetter id)

over :: Optical (->) s t a b -> (a -> b) -> s -> t
over = id

set :: Optical (->) s t a b -> b -> s -> t
set l b = l (const b)
