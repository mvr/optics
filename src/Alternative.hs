--------------------------------------------------------------------------------
-- Actions Alternative
--------------------------------------------------------------------------------

class Functor f => Summy f where
  type Comp f :: *
  summy   :: f a -> (Comp f, a)
  unsummy :: (Comp f, a) -> f a

instance Summy ((,) e) where
  type Comp ((,) e) = e
  summy = id
  unsummy = id

class Acty (ob :: k -> Constraint) where
  type Act ob (m :: k) :: * -> *
  type Composy ob :: k -> k -> k

--  assocy :: (ob m, ob n, ob (Composy ob m n)) => Proxy ob -> Act ob m (Act ob n a) -> Act ob (Composy ob m n) a

instance Acty Summy where
instance Acty Functor where
  type Act Functor f = f
  type Composy Functor = Compose


class Profunctor p => Tambary (ob :: k -> Constraint) p where
  walky :: ob m => Proxy ob -> p a b -> p (Act ob m a) (Act ob m b)
  -- ?
