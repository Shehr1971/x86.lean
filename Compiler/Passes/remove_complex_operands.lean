import Compiler.Languages.L_Var
import Compiler.Languages.L_Var_Mon

def L_Var.remove_complex_operands (e : Expr) : L_Var_Mon.Expr :=
  (remove_complex_operands_aux e 0).fst
  where 
  hoistSimple : Expr → Option L_Var_Mon.Atom
  | .var s => .some $ .var s
  | .int i => .some $ .int i
  | _ => .none
  hoistExpr (e : Expr) : StateM Nat (L_Var_Mon.Atom × (L_Var_Mon.Expr → StateM Nat L_Var_Mon.Expr)) := do
    match hoistSimple e with 
    | .some e' => pure (e', pure)
    | .none => do
      let idx ← get
      set (idx + 1)
      let tmp := .quote s!"{idx}|tmp"
      pure (.var tmp, fun body => .let tmp <$> remove_complex_operands_aux e <*> pure body)
  remove_complex_operands_aux : Expr → StateM Nat L_Var_Mon.Expr
  | .plus a b => do
    let (new_a, new_a_ctx) ← hoistExpr a
    let (new_b, new_b_ctx) ← hoistExpr b
    new_a_ctx =<< (new_b_ctx $ .plus new_a new_b)
  | .minus a b => do
    let (new_a, new_a_ctx) ← hoistExpr a
    let (new_b, new_b_ctx) ← hoistExpr b
    new_a_ctx =<< (new_b_ctx $ .minus new_a new_b)
  | .negative a => do
    let (new_a, new_a_ctx) ← hoistExpr a
    new_a_ctx $ .negative new_a
  | .let s v body => 
    .let s <$> remove_complex_operands_aux v <*> remove_complex_operands_aux body
  | .var s => pure $ .atom $ .var s
  | .int i => pure $ .atom $ .int i
  | .read => pure $ .read

#eval match L_Var.Expr.parse_expr "(let 'a 42 (let 'b 'a 'b))".iter with
  | .success _ expr => Option.some $ L_Var.remove_complex_operands expr
  | .error _ _ => Option.none

#eval match L_Var.Expr.parse_expr "(+ (read) (- 1 1))".iter with
  | .success _ expr => Option.some $ L_Var.remove_complex_operands expr
  | .error _ _ => Option.none
