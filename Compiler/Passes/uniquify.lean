import Lean.Data
import Compiler.Languages.L_Var

def L_Var.uniquify (e : Expr) : Expr :=
  (uniquify_aux e (0, .nil)).fst
  where 
  uniquify_aux : Expr → StateM (Nat × Lean.AssocList Sym Sym) Expr 
  | .plus a b => .plus <$> uniquify_aux a <*> uniquify_aux b
  | .minus a b => .minus <$> uniquify_aux a <*> uniquify_aux b
  | .negative a => .negative <$> uniquify_aux a
  | .int i => pure $ .int i
  | .read => pure $ .read
  | .var x@(.quote name) => do
    let (_, env) ← get 
    match env.find? x with
    | .some new_var => pure $ .var new_var
    | .none => pure $ .var $ .quote s!"{name}|old"
  | .let x@(.quote name) v body => do
    let (idx, env) ← get
    let new_var := .quote s!"{name}|{idx}"
    set (idx + 1, env.insert x new_var)
    Expr.let new_var <$> uniquify_aux v <*> uniquify_aux body

#eval match L_Var.Expr.parse_expr "(+ (let 'x 1 'x) (let 'x 2 'x))".iter with
  | .success _ expr => Option.some $ L_Var.uniquify expr
  | .error _ _ => Option.none
