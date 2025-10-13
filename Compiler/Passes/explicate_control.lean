import Compiler.Languages.L_Var_Mon
import Compiler.Languages.C_Var
import Compiler.Passes.remove_complex_operands

def C_Var.translate_atom : L_Var_Mon.Atom → C_Var.Atom
| .var s => .var s
| .int x => .int x

def C_Var.explicate_let : Sym → L_Var_Mon.Expr→ C_Var.Tail → C_Var.Tail
| v, .plus a b, rest => .seq (.assign v (.plus (translate_atom a) (translate_atom b))) rest
| v, .minus a b, rest => .seq (.assign v (.minus (translate_atom a) (translate_atom b))) rest
| v, .negative a, rest => .seq (.assign v (.negative $ translate_atom a)) rest
| v, .atom a, rest => .seq (.assign v (.atom $ translate_atom a)) rest
| v, .read, rest => .seq (.assign v (.read)) rest
| v, .let w e body, rest => explicate_let w e $ explicate_let v body $ rest

def C_Var.explicate_control : L_Var_Mon.Expr → C_Var.Tail
| .plus a b => .ret $ .plus (translate_atom a) (translate_atom b)
| .minus a b => .ret $ .minus (translate_atom a) (translate_atom b)
| .negative a => .ret $ .negative $ translate_atom a
| .atom a => .ret $ .atom $ translate_atom a
| .read => .ret $ .read
| .let v e body => explicate_let v e $ explicate_control body

#eval match L_Var.Expr.parse_expr "(let 'a (+ 1 (let 'c (- 1) (- 'c 42))) (let 'b 'a 'b))".iter with
  | .success _ expr => Option.some $ C_Var.explicate_control $ L_Var.remove_complex_operands expr
  | .error _ _ => Option.none
