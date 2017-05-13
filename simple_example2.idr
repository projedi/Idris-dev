import Language.Reflection.Utils
import Pruviloj
import Pruviloj.Internals

data IsEven : Nat -> Type where
  EvenZ : IsEven Z
  EvenSS : (n : Nat) -> IsEven n -> IsEven (S (S n))

total odd_not_even : (n : Nat) -> IsEven (S (n + n)) -> Void
-- odd_not_even Z EvenZ impossible
-- odd_not_even Z (EvenSS _ _) impossible
-- odd_not_even (S n) (EvenSS (n + S n) p) = odd_not_even n (rewrite (plusCommutative (S n) n) in p)

withHole : TTName -> Elab a -> Elab a
withHole hole todo = do
  focus hole
  res <- todo
  case !getHoles of
       h::_ => if h == hole then solve else fail [TextPart "hole is not in focus"]
       _ => fail [TextPart "hole is not in focus"]
  pure res

withHole' : TTName -> Elab () -> Elab ()
withHole' = withHole

fillHole : TTName -> Raw -> Elab ()
fillHole hole term = do
  withHole hole $ fill term

guessHole : TTName -> TTName -> Raw -> Elab ()
guessHole hole name type = do
  withHole' hole $ do
    claim name type
    unfocus name
    fill (Var name)

odd_not_even_S_S_lhs : Elab ()
odd_not_even_S_S_lhs = do
  [n, prf] <- apply (Var `{{Main.odd_not_even}}) [False, False]
  withHole' n $ do
    [n'] <- apply (Var `{S}) [False]
    guessHole n' `{{n}} `(Nat)
  withHole' prf $ do
    [m, p] <- apply (Var `{{Main.EvenSS}}) [False, False]
    guessHole p `{{p}} ((Var `{{Main.IsEven}}) `RApp` (Var m))
    withHole m $ do
      [mlhs, mrhs] <- apply (Var `{plus}) [False, False]
      fillHole mlhs (Var `{{n}})
      withHole mrhs $ do
        [mrhs'] <- apply (Var `{S}) [False]
        fillHole mrhs' (Var `{{n}})
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
