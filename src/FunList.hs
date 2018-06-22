data FunList a b t = Done t | More a (FunList a b (b -> t))

instance Functor (FunList a b) where
  fmap f (Done t) = Done (f t)
  fmap f (More x l) = More x (fmap (f .) l)
instance Applicative (FunList a b) where
  pure = Done
  (Done f) <*> l' = fmap f l'
  (More x l) <*> l' = More x (fmap flip l <*> l')

data Flipped b t a = Flipped { unflipped :: FunList a b t}

instance Functor (Flipped b t) where
  fmap f (Flipped (Done t)) = Flipped (Done t)
  fmap f (Flipped (More a fl)) = Flipped (More (f a) (unflipped $ fmap f (Flipped fl)))

instance Foldable (Flipped b t) where
  foldMap f (Flipped (Done t)) = mempty
  foldMap f (Flipped (More a fl)) = f a `mappend` foldMap f (Flipped fl)

instance Traversable (Flipped b t) where
  traverse f (Flipped (Done t)) = pure (Flipped (Done t))
  traverse f (Flipped (More a fl)) = ((Flipped .) . More) <$> (f a) <*> (unflipped <$> traverse f (Flipped fl))
