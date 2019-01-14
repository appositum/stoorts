module Vector

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

append : Vector n a -> Vector m a -> Vector (n + m) a
append Nil ys = ys
append (x::xs) ys = x :: append xs ys

transpose : Vector n (Vector m a) -> Vector m (Vector n a)
transpose Nil = replicate _ Nil
transpose (x::xs) = zipWith (::) x $ transpose xs
