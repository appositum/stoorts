module Stoorts.Even

%access public export
%default total

data Even : Nat -> Type where
  EvenZ : Even Z
  EvenS : Even n -> Even (S (S n))
