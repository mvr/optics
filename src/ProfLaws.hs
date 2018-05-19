{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module ProfLaws where

data HalfGuy s a where
  HalfGuy :: (s -> (m, a)) -> ((m, a) -> s) -> HalfGuy s a

data BigGuy s a where
  BigGuy :: (s -> (m, a)) -> ((m, a) -> (n, a)) -> ((n, a) -> s) -> BigGuy s a

flatten :: BigGuy s a -> (s -> a, s -> a -> a, s -> a -> a -> s)
flatten (BigGuy l c r) = (o, p, q)
  where o s = snd (l s)
        p s a = snd (c (fst (l s), a))
        q s a1 a2 = r (fst (c (fst (l s), a1)), a2)


iflatten :: BigGuy s a -> (s -> a, s -> a -> a, s -> a -> a -> s)
iflatten (BigGuy l c r) = (\s -> snd (l s), \s a -> snd (c (fst (l s), a)), \s a1 a2 -> r (fst (c (fst (l s), a1)), a2))

-- or:

-- For a lens,
get = undefined
put = undefined
-- l = \s' -> (s', get s')
-- r = \(s', a') -> put s' a'
-- rl = (\(s', a') -> (put s' a', get (put s' a')))

-- This is <l, id, r>
-- iflatten (BigGuy (\s' -> (s', get s')) id (\(s', a') -> put s' a'))
d1 = (\s -> snd ((\s' -> (s', get s')) s),
      \s a -> snd (id (fst ((\s' -> (s', get s')) s), a)),
      \s a1 a2 -> (\(s', a') -> put s' a') (fst (id (fst ((\s' -> (s', get s')) s), a1)), a2))

d2 = (\s -> get s,
      \s a -> a,
      \s a1 a2 -> put s a2)

-- This is <l, rl, r>

e1 = (\s -> snd ((\s' -> (s', get s')) s),
      \s a -> snd ((\(s', a') -> (put s' a', get (put s' a'))) (fst ((\s' -> (s', get s')) s), a)),
      \s a1 a2 -> (\(s', a') -> put s' a') (fst ((\(s', a') -> (put s' a', get (put s' a'))) (fst ((\s' -> (s', get s')) s), a1)), a2))

e2 = (\s -> get s,
      \s a -> get (put s a),
      \s a1 a2 -> put (put s a1) a2)
