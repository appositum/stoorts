module Stoorts.Fin

%access public export
%default total

data Fin : Nat -> Type where
  FZ : Fin (S n)
  FS : Fin n -> Fin (S n)

Eq (Fin n) where
  FZ == FZ = True
  (FS n) == (FS m) = n == m
  _ == _ = False
