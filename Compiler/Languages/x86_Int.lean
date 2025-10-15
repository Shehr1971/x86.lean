import Compiler.Data.Sym
import Compiler.Data.Reg
import Compiler.Data.Label
import Lean.Data

inductive x86_Int.Arg
| imm : Int → Arg
| reg : Reg → Arg
| deref : Reg → Int → Arg

instance : ToString x86_Int.Arg where
  toString : x86_Int.Arg → String
  | .imm x => s!"${x}"
  | .reg x => toString x
  | .deref reg int => s!"{int}({reg})"

inductive x86_Int.Instr
| addq: Arg → Arg → Instr
| subq: Arg → Arg → Instr
| negq: Arg → Instr
| pushq: Arg → Instr
| popq: Arg → Instr
| movq: Arg → Arg → Instr
| callq: Label → Int → Instr
| retq: Instr 
| jmp: Label → Instr

instance : ToString x86_Int.Instr where
  toString : x86_Int.Instr → String
  | .addq x y => s!"addq {x}, {y}"
  | .subq x y => s!"subq {x}, {y}"
  | .negq x => s!"negq {x}"
  | .pushq x => s!"pushq {x}"
  | .popq x => s!"popq {x}"
  | .movq x y => s!"movq {x}, {y}"
  | .callq l _ => s!"callq {l}"
  | .jmp l => s!"jmp {l}"
  | .retq => "retq"

inductive x86_Int.Block
| block: List Instr → Block

instance : ToString x86_Int.Block where
  toString : x86_Int.Block → String
  | .block instrs => String.join 
  $ instrs.map $ fun instr => s!"\t{toString instr}\n"

structure x86_Int.Info where
  locals_types : Lean.AssocList Sym Sym
  stack_space : Nat

inductive x86_Int.Program
| program: Info → List (Label × Block) → Program

instance : ToString x86_Int.Program where
  toString : x86_Int.Program → String
  | .program _ lblocks => "\n".intercalate 
  $ lblocks.map $ fun (label, block) => s!"{label}:\n{block}"
