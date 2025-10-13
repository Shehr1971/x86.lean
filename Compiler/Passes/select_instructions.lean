import Compiler.Languages.L_Var
import Compiler.Languages.C_Var
import Compiler.Languages.x86_Var
import Compiler.Passes.explicate_control
import Init.Data.List.Basic

def x86_Var.select_instructions.atom : C_Var.Atom → Arg
| .int x => .imm x
| .var x => .var x

def x86_Var.select_instructions.stmt : C_Var.Stmt → List Instr
| .assign v (.plus a b) => 
  -- book suggests this optimization, but can this case occur after we've
  -- basically converted to SSA?
  if .var v == a then [.addq (atom a) (.var v)]
  else if .var v == b then [.addq (atom b) (.var v)]
  else [.movq (atom a) (.var v), .addq (atom b) (.var v)]
| .assign v (.minus a b) => 
  if .var v == a then [.addq (atom a) (.var v)]
  else if .var v == b then [.addq (atom b) (.var v)]
  else [.movq (atom a) (.var v), .subq (atom b) (.var v)]
| .assign v (.negative a) => 
  if .var v == a then [.negq (.var v)]
  else [.movq (atom a) (.var v), .negq (.var v)]
| .assign v .read =>
  [.callq (.label "read_int") 0, .movq (.reg .rax) (.var v)]
| .assign v (.atom a) => [.movq (atom a) (.var v)]

def x86_Var.select_instructions.tail : C_Var.Tail → List Instr
| .seq assign rest => stmt assign ++ tail rest
| .ret .read => [.callq (.label "read_int") 0, .jmp (.label "fini")]
| .ret (.plus a b) => let rax := .reg .rax; [.movq (atom a) rax, .addq (atom b) rax, .jmp (.label "fini")]
| .ret (.minus a b) => let rax := .reg .rax; [.movq (atom a) rax, .subq (atom b) rax, .jmp (.label "fini")]
| .ret (.negative a) => let rax := .reg .rax; [.movq (atom a) rax, .negq rax, .jmp (.label "fini")]
| .ret (.atom a) => [.movq (atom a) (.reg .rax), .jmp (.label "fini")]

def x86_Var.select_instructions.block (c_instrs : C_Var.Tail) : Block := .block $ tail c_instrs

def x86_Var.from_C_Var : C_Var.Program → Program
| .program info tails => .program 
    { 
      locals_types := info.locals_types,
      stack_space := List.length 
        $ info.locals_types.toList.foldl 
          (fun (acc : List (Sym × Sym)) (elt : Sym × Sym) => if elt ∈ acc then acc else elt :: acc) []
        -- silly, but don't optimize prematurely
        
    } 
    (tails.map $ fun (.label l,t) => (.label l, select_instructions.block t))

#eval match L_Var.Expr.parse_expr "(+ (read) (- 1 1))".iter with
  | .success _ expr => Option.some 
  $ x86_Var.select_instructions.block
  $ C_Var.explicate_control
  $ L_Var.remove_complex_operands expr
  | .error _ _ => Option.none
