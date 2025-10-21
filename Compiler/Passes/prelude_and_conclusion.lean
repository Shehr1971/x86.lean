import Compiler.Passes.patch_instructions

def x86_Int.Program.prelude_and_conclusion : Program → Program
| .program info blocks => 
  let stack_bytes := (info.stack_space * 8) + ((info.stack_space * 8) % 16)
  .program info (blocks.append [("main", prelude_blk stack_bytes), ("fini", fini_blk stack_bytes)])
where 
  prelude_blk (stack_bytes : Nat) : Block := .block $ [
    .pushq (.reg .rbp),
    .movq (.reg .rsp) (.reg .rbp),
    .subq (.imm stack_bytes) (.reg .rsp),
    .jmp ("start")
  ]
  fini_blk (stack_bytes : Nat) : Block := .block $ [
    .addq (.imm stack_bytes) (.reg .rsp),
    .popq (.reg .rbp),
    .movq (.reg .rax) (.reg .rdi),
    .callq ("write_int") 1,
    .retq
  ]

#eval match L_Var.Expr.parse_expr "(let 'x (read) (+ (- 'x 1) 'x))".iter with
  | .success _ expr => x86_Int.Program.prelude_and_conclusion
  <$> x86_Int.Program.patch_instructions
  <$> (x86_Var.Program.assign_homes
      $ x86_Var.from_C_Var
      $ (fun tail => C_Var.Program.mk [("start", tail)])
      $ C_Var.explicate_control
      $ L_Var.remove_complex_operands expr)
  | .error _ _ => Option.none
