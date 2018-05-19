{-# LANGUAGE TupleSections #-}
import Control.Lens
import Data.Bifunctor
import Data.Profunctor
import Data.Profunctor.Strong

data Kiosk a b s t = Kiosk (s -> Either t a) (s -> b -> t)
-- (s -> Either t a) (s -> b -> t)
-- s -> (Either t a, b -> t)
-- s -> Either (t, b -> t) (a, b -> t)

sellKiosk :: Kiosk a b a b
sellKiosk = Kiosk Right (\_ -> id)

instance Profunctor (Kiosk u v) where
    dimap f g (Kiosk getter setter) = Kiosk
        (\a -> first g $ getter (f a))
        (\a v -> g (setter (f a) v))

instance Strong (Kiosk u v) where
    first' (Kiosk getter setter) = Kiosk
        (\(a, c) -> first (,c) $ getter a)
        (\(a, c) v -> (setter a v, c))

instance Choice (Kiosk u v) where
    right' (Kiosk getter setter) = Kiosk
        (\eca -> assoc (second getter eca))
        (\eca v -> second (`setter` v) eca)
      where
        assoc :: Either a (Either b c) -> Either (Either a b) c
        assoc (Left a)          = Left (Left a)
        assoc (Right (Left b))  = Left (Right b)
        assoc (Right (Right c)) = Right c

data Beh a b s t = Beh (s -> Either t (b -> t, a))

one :: Beh a b s t -> Kiosk a b s t
one (Beh f) = Kiosk getter setter
  where getter s = second snd (f s)
        setter s b = case f s of
          Left t -> t
          Right (g, _) -> g b


two :: Kiosk a b s t -> Beh a b s t
two (Kiosk getter setter) = Beh $ \s -> case getter s of
  Left t -> Left t
  Right a -> Right ((setter s), a)
