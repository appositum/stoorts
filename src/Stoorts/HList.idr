module Stoorts.HList

import Data.Fin
import Stoorts.Vector

%access public export
%default total

data HList : Vector n Type -> Type where
  Nil  : HList []
  (::) : t -> HList ts -> HList (t::ts)

ZipType : Vector n Type -> Vector n Type -> Vector n Type
ZipType [] [] = []
ZipType (x::xs) (y::ys) = (x,y) :: ZipType xs ys

ZipType3 : Vector n Type -> Vector n Type -> Vector n Type -> Vector n Type
ZipType3 [] [] [] = []
ZipType3 (x::xs) (y::ys) (z::zs) = (x,y,z) :: ZipType3 xs ys zs

zip : HList xs -> HList ys -> HList (ZipType xs ys)
zip [] [] = []
zip (x::xs) (y::ys) = (x,y) :: zip xs ys

zip3 : HList xs -> HList ys -> HList zs -> HList (ZipType3 xs ys zs)
zip3 [] [] [] = []
zip3 (x::xs) (y::ys) (z::zs) = (x,y,z) :: zip3 xs ys zs

infixl 9 !!
(!!) : HList ts -> (fin : Fin (length ts)) -> ts !! fin
(x::_) !! FZ = x
(_::xs) !! (FS n) = xs !! n

head : HList (t::ts) -> t
head (x::_) = x

tail : HList (t::ts) -> HList ts
tail (_::xs) = xs

init : HList ts -> HList (init ts)
init (_::[]) = []
init (x::y::ys) = x :: init (y::ys)

last : HList ts -> last ts
last (x::[]) = x
last (_::y::ys) = last (y::ys)

(++) : HList txs -> HList tys -> HList (txs ++ tys)
[] ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

take : (n : Nat) -> HList ts -> HList (take n ts)
take Z _ = []
take (S n) (x::xs) = x :: take n xs

drop : (n : Nat) -> HList ts -> HList (drop n ts)
drop Z xs = xs
drop (S n) (x::xs) = drop n xs

length : HList ts -> Nat
length {ts} _ = length ts

private
lengthProof : (xs : HList ts) -> length xs = length ts
lengthProof _ = Refl

toHList : (xs : List a) -> HList (replicate (length xs) a)
toHList [] = []
toHList (x::xs) = x :: toHList xs
