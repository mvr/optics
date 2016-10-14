{-# LANGUAGE GADTs #-}
-- {-# LANGUAGE TypeInType #-} -- Could this help us in interesting ways?
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Test where

import Unsafe.Coerce
import Data.Constraint

import Data.Void
import Data.Proxy
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Traversable
import Data.Profunctor
-- import Data.Profunctor.Composition

import Data.Tuple (swap)

--------------------------------------------------------------------------------
-- Questions
--------------------------------------------------------------------------------

-- Is this the morally correct form of optic families?
--   Optic families might be captured by pointwise actions on functors
--   Eg. Lens families are optics for the pointwise cartesian product:
--   C x [C, C] -> [C, C]
--   This might need Ed's `categories` to write properly

-- Is this the morally correct form of getters/reviews?
--   This is related to the above: s t a b doesn't makes sense for
--   getters/reviews?

-- Are there useful monoidal actions I am missing?

-- Are there other useful Wanderers?

-- Can I encode guarantees that:
--   Tambara (,) p               implies Tambara Trivial p
--   Tambara Either p            implies Tambara Trivial p

--   Tambara TraversableAction p implies Tambara (,) p
--   Tambara TraversableAction p implies Tambara Either p
--   Tambara CopointedAction p   implies Tambara (,) p
--   Tambara PointedAction p     implies Tambara Either p

--   Tambara FunctorAction p     implies Tambara TraversableAction p
--   Tambara FoldAction p        implies Tambara CopointedAction p
--   Tambara FoldAction p        implies Tambara TraversableAction p

--------------------------------------------------------------------------------
-- Action
--------------------------------------------------------------------------------

class Vacuous (a :: i)
instance Vacuous a

class Action (act :: k -> * -> *) where
  type ActionOb act :: k -> Constraint
  type ActionOb act = Vacuous

  type ActionCompose act (a :: k) (b :: k) :: k
  type ActionUnit    act                   :: k

  composeDict :: Proxy act ->
                 Dict (ActionOb act n) ->
                 Dict (ActionOb act m) ->
                 Dict (ActionOb act (ActionCompose act n m))
  default composeDict :: (ActionOb act ~ Vacuous) =>
                 Proxy act ->
                 Dict (ActionOb act n) ->
                 Dict (ActionOb act m) ->
                 Dict (ActionOb act (ActionCompose act n m))
  composeDict _ _ _ = Dict

  -- This could be removed with UndecidableInstances
  unitDict :: Proxy act -> Dict (ActionOb act (ActionUnit act))
  default unitDict :: (ActionOb act ~ Vacuous) =>
                      Proxy act -> Dict (ActionOb act (ActionUnit act))
  unitDict _ = Dict

  -- These coudl be Isos
  assoc   :: (ActionOb act m, ActionOb act n, ActionOb act (ActionCompose act m n)) =>
             act m (act n a) -> act (ActionCompose act m n) a
  unassoc :: (ActionOb act m, ActionOb act n, ActionOb act (ActionCompose act m n)) =>
             act (ActionCompose act m n) a -> act m (act n a)

  unit    :: act (ActionUnit act) a -> a
  ununit  :: a -> act (ActionUnit act) a

  -- Wanderer is our `ALens`, `APrism` etc
  type Wanderer act a b = (p :: * -> * -> *) | p -> act a b
  type Wanderer act a b = LoneWanderer act a b

  walkaboutish   :: Wanderer act a a x y -> LoneWanderer act a a x y
  default walkaboutish :: LoneWanderer act a a x y -> LoneWanderer act a a x y
  walkaboutish = id

  unwalkaboutish :: LoneWanderer act a a x y -> Wanderer act a a x y
  default unwalkaboutish :: LoneWanderer act a a x y -> LoneWanderer act a a x y
  unwalkaboutish = id

  {-# MINIMAL assoc, unassoc, unit, ununit #-}

------------------------------
-- Functorial

class Action act => FunctorialAction act where
  amap :: ActionOb act m => (a -> b) -> act m a -> act m b

  default amap :: Functor (act m) => (a -> b) -> act m a -> act m b
  amap = fmap

  walkabout   :: Wanderer act a b x y -> LoneWanderer act a b x y
  default walkabout :: LoneWanderer act a b x y -> LoneWanderer act a b x y
  walkabout = id

  unwalkabout :: LoneWanderer act a b x y -> Wanderer act a b x y
  default unwalkabout :: LoneWanderer act a b x y -> LoneWanderer act a b x y
  unwalkabout = id

--------------------------------------------------------------------------------
-- Exchange, Pastro, Etc
--------------------------------------------------------------------------------

data Exchange a b s t = Exchange (b -> t) (s -> a)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange l r) = Exchange (g . l) (r . f)

data Pastro act p a b where
  Pastro :: ActionOb act m => (act m y -> b) -> p x y -> (a -> act m x) -> Pastro act p a b

instance Profunctor (Pastro act p) where
  dimap f g (Pastro l m r) = Pastro (g . l) m (r . f)

-- This is just Yoneda-reduced `Pastro act (Exchange a b)`
-- Also our default `An Optic`
data LoneWanderer act a b x y where
  LoneWanderer :: ActionOb act m => (act m b -> y) -> (x -> act m a) -> LoneWanderer act a b x y

instance Profunctor (LoneWanderer act a b) where
  dimap f g (LoneWanderer l r) = LoneWanderer (g . l) (r . f)

-- Is this `sell`?
lone :: forall act a b. Action act => LoneWanderer act a b a b
lone = case unitDict (Proxy :: Proxy act) :: Dict (ActionOb act (ActionUnit act)) of
         Dict -> LoneWanderer unit ununit

-- Is this `bazaar`?
alone :: (FunctorialAction act, ActionOb act m)
         => Optical (LoneWanderer act a b) (act m x) (act m y) x y
alone (LoneWanderer (l :: act n b -> y)
                    (r :: x -> act n a)) =
  case composeDict (Proxy :: Proxy act)
                   (Dict :: Dict (ActionOb act m))
                   (Dict :: Dict (ActionOb act n)) of
    Dict -> LoneWanderer (amap l . unassoc) (assoc . amap r)
  :: forall m. ActionOb act m => LoneWanderer act a b (act m x) (act m y)

instance (FunctorialAction act) => Tambara act (LoneWanderer act a b) where
  walk = alone

--------------------------------------------------------------------------------
-- Tambara
--------------------------------------------------------------------------------

class (Action act, Profunctor p) => Tambara (act :: k -> * -> *) p where
  walk :: ActionOb act m => p a b -> p (act m a) (act m b)
  default walk :: forall m a b. (ActionOb act m, TambaraWander act p) => p a b -> p (act m a) (act m b)
  walk = wander (unwalkabout $ alone lone)

  wanderish :: (Wanderer act a a) s s -> (p a a -> p s s)
  wanderish w p = case walkaboutish w of
                  LoneWanderer l r -> dimap r l (walk p)

class (FunctorialAction act, Tambara act p) => TambaraWander act p where
  wander :: (Wanderer act a b) s t -> (p a b -> p s t)
  wander w p = case walkabout w of
                 LoneWanderer l r -> dimap r l (walk p)

instance (FunctorialAction act) => Tambara act (->) where
  walk = amap

instance (FunctorialAction act) => TambaraWander act (->)


instance (FunctorialAction act) => Tambara act (Pastro act p) where
  -- Could this duplicate `alone` less?
  walk (Pastro (l :: act n y -> b)
               (p :: p x y)
               (r :: a -> act n x))
    = case composeDict (Proxy :: Proxy act)
                       (Dict :: Dict (ActionOb act m))
                       (Dict :: Dict (ActionOb act n)) of
        Dict -> Pastro (amap l . unassoc) p (assoc . amap r)
      :: forall m. ActionOb act m => Pastro act p (act m a) (act m b)

instance (FunctorialAction act) => TambaraWander act (Pastro act p)

--------------------------------------------------------------------------------
-- Actions
--------------------------------------------------------------------------------

------------------------------
-- Trivial

class IsUnit a | -> a
instance IsUnit ()

type family ComposeUnit (a :: *) (b :: *) where
  ComposeUnit a b = ()

-- This is basically Tagged
data Trivial (u :: *) a = Trivial { unTrivial :: a } deriving Functor

instance Action Trivial where
  type ActionOb Trivial = IsUnit
  type ActionCompose Trivial a b = ComposeUnit a b
  type ActionUnit Trivial = ()

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  assoc (Trivial (Trivial a)) = Trivial a
  unassoc (Trivial a) = Trivial (Trivial a)
  unit (Trivial a) = a
  ununit a = Trivial a

  type Wanderer Trivial a b = Exchange a b
  walkaboutish = walkabout
  unwalkaboutish = unwalkabout

instance FunctorialAction Trivial where
  walkabout (Exchange l r) = LoneWanderer (l . unTrivial) (Trivial . r)
  unwalkabout (LoneWanderer l r) = Exchange (l . Trivial) (unTrivial . r)

instance Profunctor p => Tambara Trivial p where
  walk = dimap unTrivial Trivial

------------------------------
-- (,)

data Context a b x = Context (b -> x) a

instance Action (,) where
  type ActionCompose (,) a b = (a, b)
  type ActionUnit    (,) = ()
  assoc   (a, (b, c)) = ((a, b), c)
  unassoc ((a, b), c) = (a, (b, c))
  unit ((), a) = a
  ununit a = ((), a)

  type Wanderer (,) a b = Star (Context a b)
  walkaboutish = walkabout
  unwalkaboutish = unwalkabout

instance FunctorialAction (,) where
  walkabout (Star f) = LoneWanderer (\(x, b) -> let (Context g _) = f x in g b)
                                    (\x -> let (Context _ a) = f x in (x, a))
  unwalkabout (LoneWanderer l r) = Star (\x -> let (m, a) = r x in
                                                 Context (\b -> l (m, b)) a)

instance (Functor f) => Tambara (,) (Star f) where
  walk (Star f) = Star $ \ ~(c, a) -> (c,) <$> f a

------------------------------
-- Either

instance Action Either where
  type ActionCompose Either a b = Either a b
  type ActionUnit    Either = Void
  assoc (Left a)           = Left (Left a)
  assoc (Right (Left b))   = Left (Right b)
  assoc (Right (Right c))  = Right c

  unassoc (Left (Left a))  = Left a
  unassoc (Left (Right b)) = Right (Left b)
  unassoc (Right c)        = Right (Right c)

  unit (Left v) = absurd v
  unit (Right a) = a
  ununit = Right

instance FunctorialAction Either

instance (Pointed f, Functor f) => Tambara Either (Star f) where
  walk (Star f) = Star $ either (point . Left) (fmap Right . f)

------------------------------
-- Pointed

class {- Representational f =>? -} Pointed (f :: * -> *) where
  point :: a -> f a

instance Pointed Identity where
  point = Identity

instance (Pointed f, Pointed g) => Pointed (Compose f g) where
  point = Compose . point . point

instance Pointed (Either a) where
  point b = Right b

newtype PointedAction f a = PointedAction { unPointedAction :: f a }

instance Pointed f => Pointed (PointedAction f) where
  point = PointedAction . point

data Forgetter a b x y = Forgetter (x -> y) (b -> y)

instance Profunctor (Forgetter a b) where
  dimap f g (Forgetter i r) = Forgetter (g . i . f) (g . r)

instance Action PointedAction where
  type ActionOb PointedAction          = Pointed
  type ActionCompose PointedAction f g = Compose f g
  type ActionUnit PointedAction        = Identity

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  -- We just assume every Pointed is representational
  assoc   = unsafeCoerce
  unassoc = unsafeCoerce
  unit (PointedAction (Identity a)) = a
  ununit a = (PointedAction (Identity a))

  type Wanderer PointedAction a b = Forgetter a b
  walkaboutish (Forgetter i r)
    = LoneWanderer (\(PointedAction e) -> case e of
                                            Left x -> i x
                                            Right a -> r a)
                   (PointedAction . Left)
  unwalkaboutish (LoneWanderer l r) = Forgetter (l . r) (l . point)

------------------------------
-- Copointed

class {- Representational f =>? -} Copointed (f :: * -> *) where
  copoint :: f a -> a

newtype CopointedAction f a = CopointedAction { unCopointedAction :: f a }

instance Copointed f => Copointed (CopointedAction f) where
  copoint (CopointedAction fa) = copoint fa

instance Copointed Identity where
  copoint = runIdentity

instance (Copointed f, Copointed g) => Copointed (Compose f g) where
  copoint = copoint . copoint . getCompose

instance Copointed ((,) a) where
  copoint (_, b) = b

data Coforgetter a b x y = Coforgetter (x -> y) (x -> a)

instance Profunctor (Coforgetter a b) where
  dimap f g (Coforgetter i r) = Coforgetter (g . i . f) (r . f)

instance Action CopointedAction where
  type ActionOb CopointedAction          = Copointed
  type ActionCompose CopointedAction f g = Compose f g
  type ActionUnit CopointedAction        = Identity

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  assoc   = unsafeCoerce
  unassoc = unsafeCoerce
  unit (CopointedAction (Identity a)) = a
  ununit a = (CopointedAction (Identity a))

  type Wanderer CopointedAction a b = Coforgetter a b
  walkaboutish (Coforgetter i r) = LoneWanderer (\(CopointedAction (y,_)) -> y)
                                            (\x -> CopointedAction (i x, r x))
  unwalkaboutish (LoneWanderer l r) = Coforgetter (l . r) (copoint . r)

instance (Functor f, Contravariant f) => Tambara CopointedAction (Star f) where
  walk (Star f) = Star (phantom . f . copoint)
  --wander = undefined

------------------------------
-- Functor

newtype FunctorAction f a = FunctorAction { unFunctorAction :: f a }

instance Functor f => Functor (FunctorAction f) where
  fmap f (FunctorAction fa) = FunctorAction (fmap f fa)

instance Action FunctorAction where
  type ActionOb FunctorAction          = Functor
  type ActionCompose FunctorAction f g = Compose f g
  type ActionUnit FunctorAction        = Identity

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  assoc (FunctorAction mna) = FunctorAction $ Compose $ fmap unFunctorAction mna
  unassoc (FunctorAction (Compose mna)) = FunctorAction $ fmap FunctorAction mna
  unit (FunctorAction (Identity a)) = a
  ununit a = (FunctorAction (Identity a))

instance FunctorialAction FunctorAction

------------------------------
-- Traversable

newtype TraversableAction f a = TraversableAction { unTraversableAction :: f a }

instance Functor f => Functor (TraversableAction f) where
  fmap f (TraversableAction fa) = TraversableAction (fmap f fa)

newtype Bazaar a b y = Bazaar {
    runBazaar :: forall f. Applicative f => (a -> f b) -> f y
  } deriving Functor

instance Applicative (Bazaar a b) where
  pure y = Bazaar $ const $ pure y
  Bazaar k <*> Bazaar h = Bazaar (\f -> k f <*> h f)

unextract :: a -> Bazaar a y y
unextract a = Bazaar $ \f -> f a

extract :: Bazaar b b y -> y
extract (Bazaar f) = runIdentity $ f Identity

newtype Raazab b y a = Raazab { unRaazab :: Bazaar a b y }

instance Functor (Raazab b y) where
  fmap f (Raazab (Bazaar d)) = Raazab $ Bazaar $ \g -> d (g . f)

instance Foldable (Raazab b y) where
  foldMap = foldMapDefault

instance Traversable (Raazab b y) where
  traverse f (Raazab (Bazaar d))
    = fmap Raazab $
      getCompose $
      d (Compose . fmap unextract . f)

instance Action TraversableAction where
  type ActionOb TraversableAction          = Traversable
  type ActionCompose TraversableAction f g = Compose f g
  type ActionUnit TraversableAction        = Identity

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  assoc (TraversableAction mna)
    = TraversableAction $ Compose $ fmap unTraversableAction mna
  unassoc (TraversableAction (Compose mna))
    = TraversableAction $ fmap TraversableAction mna
  unit (TraversableAction (Identity a)) = a
  ununit a = (TraversableAction (Identity a))

  type Wanderer TraversableAction a b = Star (Bazaar a b)
  walkaboutish = walkabout
  unwalkaboutish = unwalkabout

instance FunctorialAction TraversableAction where
  walkabout (Star f)
    = LoneWanderer (extract . unRaazab . unTraversableAction)
                   (TraversableAction . Raazab . f)
  unwalkabout (LoneWanderer l r)
    = Star (\x -> Bazaar $
              \afb -> fmap (l . TraversableAction)
                    $ traverse afb (unTraversableAction (r x)) )

------------------------------
-- Fold - This is a guess

class {- Representational f =>? -} Foldy (f :: * -> *) where
  foldy :: Monoid a => f a -> a
  foldyDict :: Monoid a => Dict (Monoid (f a)) -- Or no monoid requiremtn on a?

instance Foldy Identity where
  foldy = runIdentity
  foldyDict = Dict

instance Monoid (f (g a)) => Monoid (Compose f g a) where
  mempty = Compose mempty
  (Compose fga) `mappend` (Compose fgb) = Compose (fga `mappend` fgb)

instance (Foldy f, Foldy g) => Foldy (Compose f g) where
  foldy (fga :: Compose f g a)
    = case foldyDict :: Dict (Monoid (g a)) of
        Dict -> foldy $ foldy $ getCompose fga

  foldyDict :: forall a. Monoid a => Dict (Monoid (Compose f g a))
  foldyDict = case foldyDict :: Dict (Monoid (g a)) of
      Dict -> case foldyDict :: Dict (Monoid (f (g a))) of
        Dict -> Dict

instance Foldy [] where
  foldy = mconcat
  foldyDict = Dict

newtype FoldyAction f a = FoldyAction { unFoldyAction :: f a }

instance Action FoldyAction where
  type ActionOb FoldyAction          = Foldy
  type ActionCompose FoldyAction f g = Compose f g
  type ActionUnit FoldyAction        = Identity

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  assoc   = unsafeCoerce
  unassoc = unsafeCoerce
  unit (FoldyAction (Identity a)) = a
  ununit a = (FoldyAction (Identity a))

--------------------------------------------------------------------------------
-- Optics
--------------------------------------------------------------------------------

type Optical p s t a b = p a b -> p s t
type Optic act s t a b = forall p. TambaraWander act p => Optical p s t a b
type Opticish act s t a b = forall p. Tambara act p => Optical p s t a b

type Iso        s t a b = Optic    Trivial           s t a b
type Lens       s t a b = Optic    (,)               s t a b
type Prism      s t a b = Optic    Either            s t a b
type Traversal  s t a b = Optic    TraversableAction s t a b
type Setter     s t a b = Optic    FunctorAction     s t a b
type Getter     s t a b = Opticish CopointedAction   s t a b
type Review     s t a b = Opticish PointedAction     s t a b
type Fold       s t a b = Opticish FoldyAction       s t a b

type Simple o s a = o s s a a

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso = dimap

_1 :: Lens (a, c) (b, c) a b
_1 = dimap swap swap . walk

_2 :: Lens (c, a) (c, b) a b
_2 = walk

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta go . walk
  where go (Left t) = t
        go (Right b) = bt b

_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just $ maybe (Left Nothing) Right

_Nothing :: Prism (Maybe a) (Maybe a) () ()
_Nothing = prism (const Nothing) $ maybe (Right ()) (Left . Just)

-- Why doesn't injectivity infer this?
to :: (s -> a) -> Getter s s a a
to f = wanderish @CopointedAction $ Coforgetter id f

unto :: (a -> s) -> Review s s a a
unto f = wanderish @PointedAction $ Forgetter id f

traverse' :: forall f a b. Traversable f => Traversal (f a) (f b) a b
traverse' = wander @TraversableAction
            $ Star $ \fa -> Bazaar (flip traverse fa)

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

view :: Optical (Star (Const a)) s t a b -> s -> a
view l = getConst . (runStar $ l (Star Const))

over :: Optical (->) s t a b -> (a -> b) -> s -> t
over = id

set :: Optical (->) s t a b -> b -> s -> t
set l b = l (const b)

-- from :: Iso s t a b -> Iso b a t s
-- from = undefined
