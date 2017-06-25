class CopointFor a f where
  copointfor :: f a -> a

class Copointish f where
  copointishDict :: Dict (CopointFor a f)

instance Action Copointish where

eqToRefl :: forall a b. (a == b) ~ 'True => a :~: b
eqToRefl = unsafeCoerce (Refl :: () :~: ())

data family Copointer' (flag :: Bool) t b x
data instance Copointer' 'True t b x = CPExtra t b
data instance Copointer' 'False t b x = CPNormal x

data Copointer t b x = Copointer (Copointer' (x == b) t b x)

class CopointerHelper (flag :: Bool) t b a where
  copointfor' :: Proxy flag -> (Copointer' flag t b a) -> a

instance ((a == b) ~ 'True) => CopointerHelper 'True t b a where
  copointfor' _ (CPExtra t b) = case eqToRefl :: a :~: b of
    Refl -> b

instance CopointerHelper 'False t b a where
  copointfor' _ (CPNormal x) = x

instance ((a == b) ~ flag, CopointerHelper flag t b a) => CopointFor a (Copointer t b) where
  copointfor (Copointer c) = copointfor' (Proxy :: Proxy flag) c

instance Copointish (Copointer t b) where
  copointishDict = Dict

-- instance CopointFor b (Copointer t b) where
--   copointfor (Copointer (CPExtra t b)) = b

-- instance CopointFor x (Copointer t b) where
--   copointfor (Copointer (CPNormal x)) = x
