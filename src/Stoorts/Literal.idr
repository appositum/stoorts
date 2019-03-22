module Stoorts.Literal

%access public export

data BinChar : Char -> Type where
  O : BinChar '0'
  I : BinChar '1'

data HexChar : Char -> Type where
  Zero  : HexChar '0'
  One   : HexChar '1'
  Two   : HexChar '2'
  Three : HexChar '3'
  Four  : HexChar '4'
  Five  : HexChar '5'
  Six   : HexChar '6'
  Seven : HexChar '7'
  Eight : HexChar '8'
  Nine  : HexChar '9'
  A     : HexChar 'A'
  B     : HexChar 'B'
  C     : HexChar 'C'
  D     : HexChar 'D'
  E     : HexChar 'E'
  F     : HexChar 'F'

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

private hexToNat : HexChar a -> Nat
hexToNat Zero  = 0
hexToNat One   = 1
hexToNat Two   = 2
hexToNat Three = 3
hexToNat Four  = 4
hexToNat Five  = 5
hexToNat Six   = 6
hexToNat Seven = 7
hexToNat Eight = 8
hexToNat Nine  = 9
hexToNat A     = 10
hexToNat B     = 11
hexToNat C     = 12
hexToNat D     = 13
hexToNat E     = 14
hexToNat F     = 15

partial x : (s : String) -> {auto p : Every HexChar (unpack s)} -> Nat
x {p} s = fromHexChars p (length s) where
  partial fromHexChars : Every HexChar xs -> Nat -> Nat
  fromHexChars [] _ = 0
  fromHexChars (x::xs) (S n) = hexToNat x * (pow 16 n) + fromHexChars xs n

private sixteen : Every HexChar (unpack "10")
sixteen = [One, Zero]

private ff : Every HexChar (unpack "FF")
ff = [F, F]
