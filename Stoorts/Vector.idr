module Stoorts.Vector

import Stoorts.Fin

%access public export
%default total

data Vector : Nat -> Type -> Type where
  Nil  : Vector Z a
  (::) : a -> Vector n a -> Vector (S n) a

Eq a => Eq (Vector n a) where
  Nil == Nil = True
  (x::xs) == (y::ys) = x == y && xs == ys

Ord a => Ord (Vector n a) where
  compare Nil Nil = EQ
  compare (x::xs) (y::ys) = compare x y `thenCompare` compare xs ys

Functor (Vector n) where
  map _ Nil = Nil
  map f (x::xs) = f x :: map f xs

replicate : (n : Nat) -> a -> Vector n a
replicate Z _ = Nil
replicate (S n) a = a :: replicate n a

Applicative (Vector n) where
  pure = replicate _

  Nil <*> Nil = Nil
  (f::fs) <*> (x::xs) = f x :: (fs <*> xs)

Foldable (Vector n) where
  foldr f z Nil = z
  foldr f z (x::xs) = f x (foldr f z xs)

Traversable (Vector n) where
  traverse _ Nil = pure Nil
  traverse f (x::xs) = (::) <$> f x <*> traverse f xs

Show a => Show (Vector n a) where
  show = show . toList

head : Vector (S n) a -> a
head (x::_) = x

tail : Vector (S n) a -> Vector n a
tail (_::xs) = xs

-- join
diagonal : Vector n (Vector n a) -> Vector n a
diagonal Nil = Nil
diagonal ((x::xs) :: xss) = x :: diagonal (tail <$> xss)

Monad (Vector n) where
  xs >>= f = diagonal $ map f xs

length : Vector n a -> Nat
length {n} _ = n

private
lengthProof : (xs : Vector n a) -> length xs = n
lengthProof _ = Refl

zipWith : (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith _ Nil Nil = Nil
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

zip : Vector n a -> Vector n b -> Vector n (a, b)
zip = zipWith MkPair

zipWith3 : (a -> b -> c -> d) -> Vector n a -> Vector n b -> Vector n c -> Vector n d
zipWith3 _ Nil Nil Nil = Nil
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

zip3 : Vector n a -> Vector n b -> Vector n c -> Vector n (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

unzip : Vector n (a, b) -> (Vector n a, Vector n b)
unzip Nil = (Nil, Nil)
unzip ((a,b)::xs) with (unzip xs)
  | (as, bs) = (a::as, b::bs)

unzip3 : Vector n (a, b, c) -> (Vector n a, Vector n b, Vector n c)
unzip3 Nil = (Nil, Nil, Nil)
unzip3 ((a,b,c)::xs) with (unzip3 xs)
  | (as, bs, cs) = (a::as, b::bs, c::cs)

(++) : Vector n a -> Vector m a -> Vector (n + m) a
Nil ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

transpose : Vector n (Vector m a) -> Vector m (Vector n a)
transpose Nil = replicate _ Nil
transpose (x::xs) = zipWith (::) x $ transpose xs

index : Fin n -> Vector n a -> a
index FZ (x::xs) = x
index (FS n) (x::xs) = index n xs

filter : (a -> Bool) -> Vector n a -> (m ** Vector m a)
filter _ Nil = (_ ** Nil)
filter p (x::xs) =
  let (_ ** rest) = filter p xs in
  if p x then (_ ** x :: rest) else (_ ** rest)

init : Vector (S n) a -> Vector n a
init (_::Nil) = Nil
init (x::y::ys) = x :: init (y::ys)

last : Vector (S n) a -> a
last (x::Nil) = x
last (_::y::ys) = last (y::ys)

take : (n : Nat) -> Vector (n + m) a -> Vector n a
take Z _ = Nil
take (S n) (x::xs) = x :: take n xs

drop : (n : Nat) -> Vector (n + m) a -> Vector m a
drop Z xs = xs
drop (S n) (_::xs) = drop n xs
