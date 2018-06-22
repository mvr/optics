{-# LANGUAGE RankNTypes #-}
module Indexed where

import Control.Monad.Indexed

data Underlying m a = Underlying { getUnderlying :: forall i. m i i a }

instance IxFunctor m => Functor (Underlying m) where
  fmap f (Underlying g) = Underlying (imap f g)

instance IxApplicative m => Applicative (Underlying m) where

instance IxMonad m => Monad (Underlying m) where
  return a = Underlying (ireturn a)
  (Underlying ma) >>= f = Underlying (ibind (getUnderlying . f) ma)
