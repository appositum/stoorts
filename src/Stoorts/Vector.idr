module Stoorts.Vector

import Data.Fin

%access public export
%default total

data Vector : Nat -> Type -> Type where
  Nil  : Vector Z a
  (::) : a -> Vector n a -> Vector (S n) a

Eq a => Eq (Vector n a) where
  [] == [] = True
  (x::xs) == (y::ys) = x == y && xs == ys

Ord a => Ord (Vector n a) where
  compare [] [] = EQ
  compare (x::xs) (y::ys) = compare x y `thenCompare` compare xs ys

Functor (Vector n) where
  map _ [] = []
  map f (x::xs) = f x :: map f xs

replicate : (n : Nat) -> a -> Vector n a
replicate Z _ = []
replicate (S n) a = a :: replicate n a

Applicative (Vector n) where
  pure = replicate _

  [] <*> [] = []
  (f::fs) <*> (x::xs) = f x :: (fs <*> xs)

Foldable (Vector n) where
  foldr f z [] = z
  foldr f z (x::xs) = f x (foldr f z xs)

Traversable (Vector n) where
  traverse _ [] = pure []
  traverse f (x::xs) = [| f x :: traverse f xs |]

Show a => Show (Vector n a) where
  show = show . toList

head : Vector (S n) a -> a
head (x::_) = x

tail : Vector (S n) a -> Vector n a
tail (_::xs) = xs

-- join
diagonal : Vector n (Vector n a) -> Vector n a
diagonal [] = []
diagonal ((x::xs) :: xss) = x :: diagonal (tail <$> xss)

Monad (Vector n) where
  xs >>= f = diagonal $ map f xs

length : Vector n a -> Nat
length {n} _ = n

private
lengthProof : (xs : Vector n a) -> length xs = n
lengthProof _ = Refl

zipWith : (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith _ [] [] = []
zipWith f (x::xs) (y::ys) = f x y :: zipWith f xs ys

zip : Vector n a -> Vector n b -> Vector n (a, b)
zip = zipWith MkPair

zipWith3 : (a -> b -> c -> d) -> Vector n a -> Vector n b -> Vector n c -> Vector n d
zipWith3 _ [] [] [] = []
zipWith3 f (x::xs) (y::ys) (z::zs) = f x y z :: zipWith3 f xs ys zs

zip3 : Vector n a -> Vector n b -> Vector n c -> Vector n (a, b, c)
zip3 = zipWith3 (\x,y,z => (x,y,z))

unzip : Vector n (a, b) -> (Vector n a, Vector n b)
unzip [] = ([], [])
unzip ((a,b)::xs) with (unzip xs)
  | (as, bs) = (a::as, b::bs)

unzip3 : Vector n (a, b, c) -> (Vector n a, Vector n b, Vector n c)
unzip3 [] = ([], [], [])
unzip3 ((a,b,c)::xs) with (unzip3 xs)
  | (as, bs, cs) = (a::as, b::bs, c::cs)

(++) : Vector n a -> Vector m a -> Vector (n + m) a
[] ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

transpose : Vector n (Vector m a) -> Vector m (Vector n a)
transpose [] = replicate _ []
transpose (x::xs) = zipWith (::) x $ transpose xs

infixl 9 !!
(!!) : Vector n a -> Fin n -> a
(x::_) !! FZ = x
(_::xs) !! (FS n) = xs !! n

filter : (a -> Bool) -> Vector n a -> (m ** Vector m a)
filter _ [] = (_ ** [])
filter p (x::xs) =
  let (_ ** rest) = filter p xs in
  if p x then (_ ** x :: rest) else (_ ** rest)

init : Vector (S n) a -> Vector n a
init (_::[]) = []
init (x::y::ys) = x :: init (y::ys)

last : Vector (S n) a -> a
last (x::[]) = x
last (_::y::ys) = last (y::ys)

take : (n : Nat) -> Vector (n + m) a -> Vector n a
take Z _ = []
take (S n) (x::xs) = x :: take n xs

drop : (n : Nat) -> Vector (n + m) a -> Vector m a
drop Z xs = xs
drop (S n) (_::xs) = drop n xs

takeWhile : (a -> Bool) -> Vector n a -> (m ** Vector m a)
takeWhile p [] = (0 ** [])
takeWhile p (x::xs) =
  let (_ ** rest) = takeWhile p xs
  in if p x then (_ ** x :: rest) else (_ ** [])

elem : Eq a => a -> Vector n a -> Bool
elem a = foldr (\x, acc => if x == a then True else acc) False

lookup : Eq k => k -> Vector n (k, v) -> Maybe v
lookup _ [] = Nothing
lookup a ((key, val) :: pairs) =
  if key == a then Just val else lookup a pairs

find : (a -> Bool) -> Vector n a -> Maybe a
find _ [] = Nothing
find p (x::xs) = if p x then Just x else find p xs
