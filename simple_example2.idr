import Pruviloj
import Pruviloj.Internals

data IsEven : Nat -> Type where
  EvenZ : IsEven Z
  EvenSS : (n : Nat) -> IsEven n -> IsEven (S (S n))

total odd_not_even : (n : Nat) -> IsEven (S (n + n)) -> Void
-- odd_not_even Z EvenZ impossible
-- odd_not_even Z (EvenSS _ _) impossible
-- odd_not_even (S n) (EvenSS (n + S n) p) = odd_not_even n (rewrite (plusCommutative (S n) n) in p)

odd_not_even_S_S_lhs : Elab ()
odd_not_even_S_S_lhs = do
  [n, prf] <- apply (Var `{{Main.odd_not_even}}) [False, False]
  -- Fill n
  focus n
  [n'] <- apply (Var `{S}) [False]
  focus n'
  claim `{{n}} `(Nat)
  unfocus `{{n}}
  fill (Var `{{n}})
  solve -- n'
  solve -- n
  -- Fill prf
  focus prf
  [m, p] <- apply (Var `{{Main.EvenSS}}) [False, False]
  focus p
  claim `{{p}} ((Var `{{Main.IsEven}}) `RApp` (Var m))
  unfocus `{{p}}
  fill (Var `{{p}})
  solve -- p
  focus m
  [mlhs, mrhs] <- apply (Var `{plus}) [False, False]
  focus mlhs
  fill (Var `{{n}})
  solve -- mlhs
  focus mrhs
  [mrhs'] <- apply (Var `{S}) [False]
  focus mrhs'
  fill (Var `{{n}})
  solve -- mrhs'
  solve -- mrhs
  solve -- m
  solve -- prf
  solve

odd_not_even_S_S_rhs : Elab ()
odd_not_even_S_S_rhs = do
  [n, prf] <- apply (Var `{{Main.odd_not_even}}) [False, False]
  -- Fill n
  focus n
  fill (Var `{{n}})
  solve -- n
  -- Fill prf
  focus prf
  fill (Var `{{p}})
  solve -- prf
  solve

odd_not_even_S_S : Elab (FunClause Raw)
odd_not_even_S_S = elabPatternClause odd_not_even_S_S_lhs odd_not_even_S_S_rhs

odd_not_even_impl : Elab ()
odd_not_even_impl = do
  clSS <- odd_not_even_S_S
  defineFunction $ DefineFun `{{Main.odd_not_even}} [clSS]

%runElab odd_not_even_impl
