module Stoorts.HList

import Data.Fin
import Stoorts.Vector

%access public export
%default total

data HList : (n : Nat) -> Vector n Type -> Type where
  Nil  : HList Z []
  (::) : t -> HList n ts -> HList (S n) (t::ts)

ZipType : Vector n Type -> Vector n Type -> Vector n Type
ZipType [] [] = []
ZipType (x::xs) (y::ys) = (x,y) :: ZipType xs ys

ZipType3 : Vector n Type -> Vector n Type -> Vector n Type -> Vector n Type
ZipType3 [] [] [] = []
ZipType3 (x::xs) (y::ys) (z::zs) = (x,y,z) :: ZipType3 xs ys zs

zip : HList n xs -> HList n ys -> HList n (ZipType xs ys)
zip [] [] = []
zip (x::xs) (y::ys) = (x,y) :: zip xs ys

zip3 : HList n xs -> HList n ys -> HList n zs -> HList n (ZipType3 xs ys zs)
zip3 [] [] [] = []
zip3 (x::xs) (y::ys) (z::zs) = (x,y,z) :: zip3 xs ys zs

index : (fin : Fin n) -> HList n ts -> index fin ts
index FZ (x::_) = x
index (FS n) (_::xs) = index n xs

head : HList (S n) (t::ts) -> t
head (x::_) = x

tail : HList (S n) (t::ts) -> HList n ts
tail (_::xs) = xs

init : HList (S n) ts -> HList n (init ts)
init (_::[]) = []
init (x::y::ys) = x :: init (y::ys)

last : HList (S n) ts -> last ts
last (x::[]) = x
last (_::y::ys) = last (y::ys)

(++) : HList n txs -> HList m tys -> HList (n + m) (txs ++ tys)
[] ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

take : (n : Nat) -> HList (n + m) ts -> HList n (take n ts)
take Z _ = []
take (S n) (x::xs) = x :: take n xs

drop : (n : Nat) -> HList (n + m) ts -> HList m (drop n ts)
drop Z xs = xs
drop (S n) (x::xs) = drop n xs

length : HList n ts -> Nat
length {n} _ = n

private
lengthProof : (xs : HList n ts) -> length xs = n
lengthProof _ = Refl

private
lengthProof' : (xs : HList n ts) -> length xs = length ts
lengthProof' _ = Refl

toHList : (xs : List a) -> let len = length xs in HList len (replicate len a)
toHList [] = []
toHList (x::xs) = x :: toHList xs
