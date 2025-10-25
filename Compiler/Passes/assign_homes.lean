import Compiler.Passes.build_interference
import Compiler.Languages.x86_Int

-- making no particular effort to be efficient here
def x86_Var.graph_to_coloring (edges : List ((Sym⊕ Reg) × (Sym⊕ Reg))) : List (Sym⊕ Reg) → Coloring
| verticies => accumulate_coloring verticies initial_coloring
where 
accumulate_coloring : List (Sym⊕ Reg) → Coloring → Coloring
| [], coloring => coloring
| verticies@(x::xs), coloring => 
  let l := mostSaturated coloring x xs
  let f := firstAvailable coloring (adjacent l)
  let new_verticies := verticies.erase l
  --hack to prove termination; second case is impossible
  if new_verticies.length < verticies.length 
  then accumulate_coloring new_verticies (coloring.insert l f)
  else .nil
termination_by l => l.length
mostSaturated : Coloring → Sym⊕ Reg → List (Sym⊕ Reg) → Sym⊕ Reg
| ________, x, [] => x
| coloring, _, v::vs =>
  let l := mostSaturated coloring v vs 
  if saturatution coloring l < saturatution coloring v then v else l
countUnique {α} [BEq α] : List α → List α → Nat
| _, [] => 0
| seen, x::xs => if seen.elem x then countUnique seen xs else countUnique (x::seen) xs  + 1
adjacent : Sym⊕ Reg → List (Sym⊕ Reg)
| vertex => 
  let adjacent_edges := edges.filter fun (s,t) => s == vertex || t == vertex
  adjacent_edges.map fun (s,t) => if s == vertex then t else s
saturatution : Coloring → Sym⊕ Reg → Nat
| coloring, vertex => countUnique [] $
  let mcolors := (adjacent vertex).map coloring.find?
  mcolors.reduceOption
firstAvailable : Coloring → List (Sym⊕ Reg) → Nat
| coloring, neighbors =>
  let mcolors := neighbors.map (coloring.find? >=> Int.toNat?)
  let forbidden_colors := (mcolors.reduceOption.filter (. >= 0)).mergeSort
  forbidden_colors.foldl (fun acc c => if c == acc then acc + 1 else acc) 0

def x86_Var.Arg.assign_homes : Coloring → x86_Var.Arg → Option x86_Int.Arg
| _, .imm i => pure $ .imm i
| _, .reg r => pure $ .reg r
| _, .deref r i => pure $ .deref r i
| coloring, .var s => match coloring.find? (.inl s) with
  | .none => .none
  | .some i => match decoloring.find? i with
    | .some r => pure $ .reg r
    | .none => pure $ x86_Int.Arg.deref .rbp (((i : Int) - 10) * -8)
where 
decoloring : Lean.AssocList Int Reg := 
  .cons 10 %r14 $
  .cons 9 %r13 $
  .cons 8 %r12 $
  .cons 7 %rbx $
  .cons 6 %r10 $
  .cons 5 %r9 $
  .cons 4 %r8 $
  .cons 3 %rdi $
  .cons 2 %rsi $
  .cons 1 %rdx $
  .cons 0 %rcx $
  .cons (-1 : Int) %rax $
  .cons (-2 : Int) %rsp $
  .cons (-3 : Int) %rbp $
  .cons (-4 : Int) %r11 $
  .cons (-5 : Int) %r15 $
  .nil

def x86_Var.Instr.assign_homes : Coloring → x86_Var.Instr → Option x86_Int.Instr
| l, .addq a b => .addq <$> Arg.assign_homes l a <*> Arg.assign_homes l b
| l, .subq a b => .subq <$> Arg.assign_homes l a <*> Arg.assign_homes l b
| l, .negq a => .negq <$> Arg.assign_homes l a
| l, .pushq a => .pushq <$> Arg.assign_homes l a
| l, .popq a => .popq <$> Arg.assign_homes l a
| l, .movq a b => .movq <$> Arg.assign_homes l a <*> Arg.assign_homes l b
| _, .callq l n => pure $ .callq l n
| _, .jmp l => pure $ .jmp l 
| _, .retq => pure $ .retq

def x86_Var.Block.assign_homes : Coloring → x86_Var.Block → Option x86_Int.Block
| l, .block _ instrs => .block <$> instrs.mapM (fun i => Instr.assign_homes l i)

def x86_Var.Program.assign_homes : x86_Var.Program → Option x86_Int.Program
| .program info blocks => 
  match info.stack_space with
  | .some ss => .program { locals_types := info.locals_types, stack_space := ss } <$> blocks.mapM (redoBlock info)
  | .none => .none
where 
redoBlock : PInfo → (Label × Block)  →  Option (Label×x86_Int.Block)
| info, (l, b) => do
  let graph ← info.conflicts
  let coloring := graph_to_coloring graph (b.toVars.map .inl)
  (.,.) <$> pure l <*> Block.assign_homes coloring b

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

private def verticies : List (Sym⊕ Reg) := [ &t, &v, &w, &x, &y, &z ].map .inl

#eval 
  let graph := block.uncover_live.build_interference
  (x86_Var.graph_to_coloring graph verticies).toList

#eval match L_Var.Expr.parse_expr "(let 'x (read) (+ (- 'x 1) 'x))".iter with
  | .success _ expr => x86_Var.Program.assign_homes
  $ x86_Var.Program.build_interference
  $ x86_Var.Program.uncover_live
  $ x86_Var.from_C_Var
  $ (fun tail => C_Var.Program.mk [("start", tail)])
  $ C_Var.explicate_control
  $ L_Var.remove_complex_operands expr
  | .error _ _ => Option.none

