------------------------------
-- Copointish

class {- Representational f =>? -} Copointish v (f :: * -> *) where
  copointish :: f a -> v

instance Copointish v (Const v) where
  copointish = getConst

instance (Copointish v f) => Copointish v (Compose f g) where
  copointish (Compose fga) = copointish fga

instance Copointish v ((,) v) where
  copointish (v, _) = v

newtype CopointishAction (v :: *) f a = CopointishAction { unCopointishAction :: f a }

instance Copointish v f => Copointish v (CopointishAction v f) where
  copointish (CopointishAction fa) = copointish fa

newtype Coforgetter v a b x y = Coforgetter { runCoforgetter :: x -> v }

instance Profunctor (Coforgetter v a b) where
  dimap f _ (Coforgetter r) = Coforgetter (r . f)

instance Tambara (CopointishAction v) (Coforgetter v a b) where
  walk (Coforgetter r) = Coforgetter copointish

instance Action (CopointishAction v) where
  type ActionOb      (CopointishAction v)     = Copointish v
  type ActionCompose (CopointishAction v) f g = Compose f g
  type ActionUnit    (CopointishAction v)     = ((,) v)

  composeDict _ Dict Dict = Dict
  unitDict _ = Dict

  assoc   = unsafeCoerce
  unassoc = unsafeCoerce
  unit (CopointishAction (_, a)) = a
  ununit _ = undefined

  type Wanderer (CopointishAction v) a b = Coforgetter v a b
  walkabout (Coforgetter r) = LoneWanderer _ (Const . r)
  -- walkabout (Coforgetter r) = LoneWanderer (\(CopointedAction (y,_)) -> y) undefined
  -- unwalkabout (LoneWanderer l r) = Coforgetter undefined
