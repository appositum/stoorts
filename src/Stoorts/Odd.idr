module Stoorts.Odd

%access public export
%default total

data Odd : Nat -> Type where
  OddZ : Odd (S Z)
  OddS : Odd n -> Odd (S (S n))
