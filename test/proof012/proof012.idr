import Data.Vect

vecPrf : Vect (1 + n) a = Vect (n + 1) a
vecPrf {n} = rewrite (plusCommutative 1 n) in Refl

head : Vect (n + 1) a -> a
head (rewrite vecPrf in (x :: _)) = x
