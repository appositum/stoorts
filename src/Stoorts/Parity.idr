module Stoorts.Parity

%access public export
%default total

data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd  : Parity (S (n + n))

private
proofEven : (n : Nat) -> Parity (S n + S n) -> Parity (S (S (n + n)))
proofEven n p = rewrite plusSuccRightSucc n n in p

private
proofOdd : (n : Nat) -> Parity (S (S (n + S n))) -> Parity (S (S (S (n + n))))
proofOdd n p = rewrite plusSuccRightSucc n n in p

parity : (n : Nat) -> Parity n
parity Z = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S n)) with (parity n)
  parity (S (S (m + m))) | Even = proofEven m (Even {n=S m})
  parity (S (S (S (m + m)))) | Odd = proofOdd m (Odd {n=S m})
