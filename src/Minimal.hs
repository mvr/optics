{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Wat where

-- Something like

r :: MLens (StateT a m) (ReaderT a ?)

(StateT a m) ~ foo (ReaderT a ?)
