import Pruviloj
import Pruviloj.Internals

-- id' : (a : Type) -> (x : a) -> a
-- id' a x = x

id'_decl : Elab ()
id'_decl = declareType $
             Declare `{{id'}}
               [ MkFunArg `{{a}} `(Type) Explicit NotErased
               , MkFunArg `{{x}} (Var `{{a}}) Explicit NotErased
               ]
             (Var `{{a}})

id'_lhs : Elab ()
id'_lhs = do
  [a, x] <- apply (Var `{{id'}}) [False, False]
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
  defineFunction $ DefineFun `{{id'}} [cl]

%runElab (do
         id'_decl
         id'_impl
         )
