import Pruviloj
import Pruviloj.Internals

id' : (a : Type) -> (x : a) -> a

id'_lhs : Elab ()
id'_lhs = do
  [a, x] <- apply (Var `{{Main.id'}}) [False, False]
  -- Fill a
  focus a
  claim `{{a}} `(Type)
  unfocus `{{a}}
  fill (Var `{{a}})
  solve
  -- Fill x
  focus x
  claim `{{x}} (Var `{{a}})
  unfocus `{{x}}
  fill (Var `{{x}})
  solve
  -- Fill id' a x
  solve

id'_rhs : Elab ()
id'_rhs = do
  fill (Var `{{x}})
  solve

id'_clause : Elab (FunClause Raw)
id'_clause = elabPatternClause id'_lhs id'_rhs

id'_impl : Elab ()
id'_impl = do
  cl <- id'_clause
  defineFunction $ DefineFun `{{Main.id'}} [cl]

%runElab (do
         id'_impl
         )
