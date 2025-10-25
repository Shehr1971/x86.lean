import Compiler.Passes.assign_homes

def x86_Int.Instr.patch_instructions : Instr → List Instr
| .addq a@(.deref _ _) b@(.deref _ _) => [
  .movq a %rax,
  .addq %rax b
  ]
| i => [i]

def x86_Int.Block.patch_instructions : Block → Block
| .block instrs => .block (instrs.map $ fun i => i.patch_instructions).flatten

def x86_Int.Program.patch_instructions : Program → Program
| .program info lblocks => .program info 
$ lblocks.map $ fun (l,b) => (l, b.patch_instructions)

#eval match L_Var.Expr.parse_expr "(let 'x (read) (+ (- 'x 1) 'x))".iter with
  | .success _ expr => x86_Int.Program.patch_instructions
  <$> (x86_Var.Program.assign_homes
      $ x86_Var.Program.build_interference
      $ x86_Var.Program.uncover_live
      $ x86_Var.from_C_Var
      $ (fun tail => C_Var.Program.mk [("start", tail)])
      $ C_Var.explicate_control
      $ L_Var.remove_complex_operands expr)
  | .error _ _ => Option.none
