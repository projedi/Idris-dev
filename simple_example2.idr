data IsEven : Nat -> Type where
  EvenZ : IsEven Z
  EvenSS : (n : Nat) -> IsEven n -> IsEven (S (S n))

total odd_not_even : (n : Nat) -> IsEven (S (n + n)) -> Void
odd_not_even Z EvenZ impossible
odd_not_even Z (EvenSS _ _) impossible
odd_not_even (S n) (EvenSS _ p) = odd_not_even n (rewrite (plusCommutative (S n) n) in p)
