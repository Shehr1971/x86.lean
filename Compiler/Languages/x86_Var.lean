import Compiler.Data.Sym
import Compiler.Data.Label
import Compiler.Data.Reg
import Lean.Data

inductive x86_Var.Arg
| imm : Int → Arg
| reg : Reg → Arg
| deref : Reg → Int → Arg
| var : Sym → Arg
deriving BEq

instance instToStringReg_x86_Var : ToString x86_Var.Arg where
  toString : x86_Var.Arg → String
  | .imm x => s!"${x}"
  | .reg x => toString x
  | .deref reg int => s!"{int}({reg})"
  | .var s => s!"{s}"

inductive x86_Var.Instr
| addq: Arg → Arg → Instr
| subq: Arg → Arg → Instr
| negq: Arg → Instr
| pushq: Arg → Instr
| popq: Arg → Instr
| movq: Arg → Arg → Instr
| callq: Label → Nat → Instr -- Nat indicates arity of function
| retq: Instr 
| jmp: Label → Instr

instance instToStringInstr_x86_Var : ToString x86_Var.Instr where
  toString : x86_Var.Instr → String
  | .addq x y => s!"addq {x}, {y}"
  | .subq x y => s!"subq {x}, {y}"
  | .negq x => s!"negq {x}"
  | .pushq x => s!"pushq {x}"
  | .popq x => s!"popq {x}"
  | .movq x y => s!"movq {x}, {y}"
  | .callq l x => s!"callq {l}, {x}"
  | .jmp l => s!"jmp {l}"
  | .retq => "retq"

structure x86_Var.BInfo where
  live_before : Option (List (List (Sym⊕ Reg)))

inductive x86_Var.Block
| block: BInfo → List Instr → Block

instance instToStringBlock_x86_Var : ToString x86_Var.Block where
  toString : x86_Var.Block → String
  | .block _ instrs => String.join 
  $ instrs.map $ fun instr => s!"\t{toString instr}\n"

structure x86_Var.PInfo where
  locals_types : Lean.AssocList Sym Sym
  stack_space : Nat

inductive x86_Var.Program
| program: PInfo → List (Label × Block) → Program

instance instToStringProgram_x86_Var : ToString x86_Var.Program where
  toString : x86_Var.Program → String
  | .program _ lblocks => "\n".intercalate 
  $ lblocks.map $ fun (label, block) => s!"{label}:\n{block}"
