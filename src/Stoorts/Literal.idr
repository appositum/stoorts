module Stoorts.Literal

%access public export

data BinChar : Char -> Type where
  O : BinChar '0'
  I : BinChar '1'

using (a : Type, P : a -> Type)
  data Every : (a -> Type) -> List a -> Type where
    Nil  : Every P []
    (::) : P x -> Every P xs -> Every P (x :: xs)

partial b : (s : String) -> {auto p : Every BinChar (unpack s)} -> Nat
b {p} s = fromBinChars p (length s) where
  partial fromBinChars : Every BinChar xs -> Nat -> Nat
  fromBinChars [] _ = 0
  fromBinChars (O :: xs) (S n) = fromBinChars xs n
  fromBinChars (I :: xs) (S n) = pow 2 n + fromBinChars xs n

private eight : Every BinChar (unpack "1000")
eight = [I,O,O,O]
