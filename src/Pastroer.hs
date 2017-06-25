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
module Pastroer where

import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor
import Data.Void

class (c Identity) => Action (c :: (* -> *) -> Constraint) where

  composeDict :: Dict (c f) ->
                 Dict (c g) ->
                 Dict (c (Compose f g))

class (Action c) => FunctorialAction c where
  functorialDict :: c f => Dict (Functor f)

class (Action c, Profunctor p) => Tambara c p where
  walk :: c f => p a b -> p (f a) (f b)
