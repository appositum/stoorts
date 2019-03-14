module Stoorts.Even

%access public export

data Even : Nat -> Type where
  EvenZ : Even Z
  EvenS : Even n -> Even (S (S n))

add : Even n -> Even m -> Even (n + m)
add EvenZ m = m
add (EvenS n) m = EvenS (add n m)