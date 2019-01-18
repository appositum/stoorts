module Stoorts.HList

import Stoorts.Fin
import Stoorts.Vector

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

init : HList (S n) ts -> HList n (init ts)
init (_::Nil) = Nil
init (x::y::ys) = x :: init (y::ys)

last : HList (S n) ts -> last ts
last (x::Nil) = x
last (_::y::ys) = last (y::ys)

(++) : (xs : HList n txs) -> (ys : HList m tys) -> HList (n + m) (txs ++ tys)
Nil ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)

length : HList n ts -> Nat
length {ts} _ = length ts
