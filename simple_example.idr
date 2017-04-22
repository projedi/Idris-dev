-- id' : (a : Type) -> (x : a) -> a
-- id' a x = x

id'_decl : Elab ()
id'_decl = declareType $
             Declare `{{id'}}
               [ MkFunArg `{{a}} `(Type) Explicit NotErased
               , MkFunArg `{{x}} (Var `{{a}}) Explicit NotErased
               ]
             (Var `{{a}})

id'_lhs : Raw
id'_lhs =
  RBind `{{a}} (PVar `(Type)) $
  RBind `{{x}} (PVar (Var `{{a}})) $
    ((Var `{{id'}}) `RApp` (Var `{{a}})) `RApp` (Var `{{x}})

id'_rhs : Raw
id'_rhs =
  RBind `{{a}} (PVar `(Type)) $
  RBind `{{x}} (PVar (Var `{{a}})) $
    Var `{{x}}

id'_impl : Elab ()
id'_impl = defineFunction $ DefineFun `{{id'}} [MkFunClause id'_lhs id'_rhs]

%runElab (do
         id'_decl
         id'_impl
         )
