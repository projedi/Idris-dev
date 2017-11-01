data Nat = Z | S Nat

total
plus : Nat -> Nat -> Nat
plus Z n = n
plus (S n) m = S (plus n m)

total
plusCommutative : (n : Nat) -> (m : Nat) -> (plus n m = plus m n)
plusCommutative Z Z = Refl
plusCommutative Z (S m) = rewrite plusCommutative Z m in Refl
plusCommutative (S n) Z = rewrite plusCommutative n Z in Refl
plusCommutative (S n) (S m) = rewrite plusCommutative n (S m) in rewrite sym (plusCommutative (S n) m) in rewrite plusCommutative n m in Refl

data Vect : (n : Nat) -> (a : Type) -> Type where
  Nil : Vect Z a
  Cons : a -> Vect n a -> Vect (S n) a

total
vecPrf : (a : Type) -> (n : Nat) -> Vect (plus n (S Z)) a = Vect (S n) a
vecPrf _ n = rewrite (plusCommutative (S Z) n) in Refl

head : (a : Type) -> (n : Nat) -> (xs : Vect (plus n (S Z)) a) -> a
head a n (rewrite (vecPrf a n) in (Cons x xs)) = x

{-
head : (a : Type) -> (n : Nat) -> (xs : Vect (plus (S Z) n) a) -> a
head a n (Cons x xs) = x
-}
