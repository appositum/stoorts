module HList

import Fin
import Vector

%access public export
%default total

data HList : (n : Nat) -> Vector n Type -> Type where
  Nil  : HList Z []
  (::) : t -> HList n ts -> HList (S n) (t::ts)

get : (fin : Fin n) -> HList n ts -> index fin ts
get FZ (x::_) = x
get (FS n) (_::xs) = get n xs

head : HList (S n) (t::ts) -> t
head (x::_) = x

tail : HList (S n) (t::ts) -> HList n ts
tail (_::xs) = xs

(++) : (xs : HList n txs) -> (ys : HList m tys) -> HList (n + m) (txs ++ tys)
Nil ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)
