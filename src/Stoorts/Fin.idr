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

Ord (Fin n) where
  compare FZ FZ = EQ
  compare FZ (FS _) = LT
  compare (FS _) FZ = GT
  compare (FS n) (FS m) = compare n m

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z (S n) = Just FZ
natToFin (S k) (S n) with (natToFin k n)
  | Just n' = Just (FS n')
  | Nothing = Nothing
natToFin _ _ = Nothing

finToNat : Fin n -> Nat
finToNat FZ = 0
finToNat (FS n) = 1 + finToNat n
