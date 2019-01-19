module Stoorts.HList

import Stoorts.Fin
import Stoorts.Vector

%access public export
%default total

data HList : (n : Nat) -> Vector n Type -> Type where
  Nil  : HList Z []
  (::) : t -> HList n ts -> HList (S n) (t::ts)

ZipType : Vector n Type -> Vector n Type -> Vector n Type
ZipType Nil Nil = Nil
ZipType (x::xs) (y::ys) = (x,y) :: ZipType xs ys

zip : HList n xs -> HList n ys -> HList n (ZipType xs ys)
zip Nil Nil = Nil
zip (x::xs) (y::ys) = (x,y) :: zip xs ys

get : (fin : Fin n) -> HList n ts -> index fin ts
get FZ (x::_) = x
get (FS n) (_::xs) = get n xs

head : HList (S n) (t::ts) -> t
head (x::_) = x

tail : HList (S n) (t::ts) -> HList n ts
tail (_::xs) = xs

init : HList (S n) ts -> HList n (init ts)
init (_::Nil) = Nil
init (x::y::ys) = x :: init (y::ys)

last : HList (S n) ts -> last ts
last (x::Nil) = x
last (_::y::ys) = last (y::ys)

(++) : HList n txs -> HList m tys -> HList (n + m) (txs ++ tys)
Nil ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

length : HList n ts -> Nat
length {n} _ = n

private
lengthProof : (xs : HList n ts) -> length xs = n
lengthProof _ = Refl

private
lengthProof' : (xs : HList n ts) -> length xs = length ts
lengthProof' _ = Refl
