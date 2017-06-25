data IsEven : Nat -> Type where
  IsEvenZ : IsEven Z
  IsEvenSS : IsEven n -> IsEven (S (S n))

total
odd_not_even : (n : Nat) -> IsEven (1 + n + n) -> Void
odd_not_even _ IsEvenZ impossible
odd_not_even Z (IsEvenSS _) impossible
odd_not_even (S k) (IsEvenSS p) = odd_not_even k (rewrite plusCommutative (S k) k in p)

total
rewriteHelper : (k : Nat) -> (S k + S k + 1) = S (S (k + S k))
rewriteHelper k = rewrite plusCommutative (plus k (S k)) 1 in Refl

total
odd_not_even' : (n : Nat) -> IsEven (n + n + 1) -> Void
odd_not_even' Z IsEvenZ impossible
odd_not_even' Z (IsEvenSS _) impossible
odd_not_even' (S _) IsEvenZ impossible
odd_not_even' (S k) (rewrite rewriteHelper k in IsEvenSS p) = ?odd_not_even_impl
