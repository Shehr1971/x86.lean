import Compiler.Passes.uncover_live

/-- compute interference takes an instruction and its live-after set, and
    returns a list of edges representing the interference between locations 
    implied by their interactions -/
def x86_Var.Instr.compute_interference : Instr → List (Sym⊕ Reg) → List ((Sym⊕ Reg) × (Sym⊕ Reg))
| .movq s d@(.reg r), locs => (locs.filter fun loc => toArg loc != d && toArg loc != s).map fun loc => (loc, .inr r)
| .movq s d@(.var v), locs => (locs.filter fun loc => toArg loc != d && toArg loc != s).map fun loc => (loc, .inl v)
| .movq _ _, _=> []
| i, locs => -- yuck, should be monadic
    let to_interferences written := (locs.filter fun loc => loc != written).map fun loc => (loc, written)
    (i.write_set.map to_interferences).flatten
where toArg : Sym⊕ Reg → Arg
| .inl v => .var v
| .inr r => .reg r

def x86_Var.Block.build_interference : Block → List ((Sym⊕ Reg) × (Sym⊕ Reg))
| .block info instrs => match info.live_before with
  | .some lb => (((lb.drop 1).zip instrs).map fun (locs, instr) => instr.compute_interference locs).flatten
  | .none => []

def Coloring : Type := Lean.AssocList (Sym⊕ Reg) Int

def initial_coloring : Coloring := 
  .cons (.inr %r14) 10 $
  .cons (.inr %r13) 9 $
  .cons (.inr %r12) 8 $
  .cons (.inr %rbx) 7 $
  .cons (.inr %r10) 6 $
  .cons (.inr %r9 ) 5 $
  .cons (.inr %r8 ) 4 $
  .cons (.inr %rdi) 3 $
  .cons (.inr %rsi) 2 $
  .cons (.inr %rdx) 1 $
  .cons (.inr %rcx) 0 $
  .cons (.inr %rax) (-1 : Int) $
  .cons (.inr %rsp) (-2 : Int) $
  .cons (.inr %rbp) (-3 : Int) $
  .cons (.inr %r11) (-4 : Int) $
  .cons (.inr %r15) (-5 : Int) $
  .nil


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

def x86_Var.Program.build_interference : Program → Program
| .program info blocks => 
  let conflicts := (blocks.map fun (_,b) => b.build_interference).flatten
  .program { info with conflicts := conflicts } blocks

#eval block.uncover_live.build_interference
