import Compiler.Passes.select_instructions

def x86_Var.Arg.location : Arg → List (Sym⊕ Reg)
| .reg r => [.inr r]
| .var s => [.inl s]
--XXX: x86_Var technically includes dereference arguments. Should those really be part of x86_Var?
| _ => []

def x86_Var.Instr.read_set : Instr → List (Sym⊕ Reg)
--Reads args passed, depends on function arity
| .callq _ n => .inr <$> [.rdi, .rsi, .rdx, .rcx, .r8, .r9].take n
| .movq s _ => Arg.location s
| .addq s l => Arg.location s ++ Arg.location l
| .subq s l => Arg.location s ++ Arg.location l
| .negq s => Arg.location s
| .popq _ => []
| .pushq s => Arg.location s
| .retq => []
-- special case until we have more control flow analysis
| .jmp "conclusion" => .inr <$> [.rax, .rsp]
| .jmp _ => []

def x86_Var.Instr.write_set : Instr → List (Sym⊕ Reg)
--caller saved registers can be freely written by callq
| .callq _ _ => .inr <$> [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
| .movq _ s => Arg.location s
| .addq _ s => Arg.location s
| .subq _ s => Arg.location s
| .negq s => Arg.location s
| .popq s => Arg.location s
| .pushq _ => []
| .retq => []
| .jmp _ => []

def x86_Var.Block.uncover_live : Block → Block
| .block _ instrs => .block {
    live_before := .some (instrs.reverse.foldl update_live [])
  } instrs
-- update_live computes the live_before set of a given instruction, using the
-- live_before sets of the subsequent instructions (which come earlier in the
-- reversed list).
where update_live : List (List (Sym⊕ Reg)) → Instr → List (List (Sym⊕ Reg)) 
| [], instr => [instr.read_set]
| acc@(x::_), instr => (x.filter (fun loc => ¬(instr.write_set.elem loc)) ++ instr.read_set)::acc

def x86_Var.Program.uncover_live : Program → Program
| .program info blocks => .program info $ blocks.map fun (l,b) => (l,b.uncover_live)

private def block : x86_Var.Block := 
  .block { live_before := .none } [
  .movq 1 &v,
  .movq 42 &w,
  .movq &v &x,
  .addq 7 &x,
  .movq &x &y,
  .movq &x &z,
  .addq &w &z,
  .movq &y &t,
  .negq &t,
  .movq &z %rax,
  .addq &t %rax,
  .jmp "conclusion"
  ]

#eval 
  match block.uncover_live with 
  | .block info _ => info.live_before
