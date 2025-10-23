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

def x86_Var.uncover_live : Block → Block
| .block _ instrs => .block {
    live_before := .some (instrs.reverse.foldl update_live [])
  } instrs
-- update_live computes the live_before set of a given instruction, using the
-- live_before sets of the subsequent instructions (which come earlier in the
-- reversed list).
where update_live : List (List (Sym⊕ Reg)) → Instr → List (List (Sym⊕ Reg)) 
| [], instr => [instr.read_set]
| acc@(x::_), instr => (x.filter (fun loc => ¬(instr.write_set.elem loc)) ++ instr.read_set)::acc

/-- compute interference takes an instruction and its live-after set, and
    returns a list of edges representing the interference between locations 
    implied by their interactions -/
def x86_Var.compute_interference : Instr → List (Sym⊕ Reg) → List ((Sym⊕ Reg) × (Sym⊕ Reg))
| .movq s d@(.reg r), locs => (locs.filter fun loc => toArg loc != d && toArg loc != s).map fun loc => (loc, .inr r)
| .movq s d@(.var v), locs => (locs.filter fun loc => toArg loc != d && toArg loc != s).map fun loc => (loc, .inl v)
| .movq _ _, _=> []
| i, locs => -- yuck, should be monadic
    let to_interferences written := (locs.filter fun loc => loc != written).map fun loc => (loc, written)
    (i.write_set.map to_interferences).flatten
where toArg : Sym⊕ Reg → Arg
| .inl v => .var v
| .inr r => .reg r

def x86_Var.interference_for_block : Block → List ((Sym⊕ Reg) × (Sym⊕ Reg))
| .block info instrs => match info.live_before with
  | .some lb => (((lb.drop 1).zip instrs).map fun (locs, instr) => compute_interference instr locs).flatten
  | .none => []

def Coloring : Type := Lean.AssocList (Sym⊕ Reg) Int

def initial_coloring : Coloring := 
  .cons (.inr .r14) 10 $
  .cons (.inr .r13) 9 $
  .cons (.inr .r12) 8 $
  .cons (.inr .rbx) 7 $
  .cons (.inr .r10) 6 $
  .cons (.inr .r9 ) 5 $
  .cons (.inr .r8 ) 4 $
  .cons (.inr .rdi) 3 $
  .cons (.inr .rsi) 2 $
  .cons (.inr .rdx) 1 $
  .cons (.inr .rcx) 0 $
  .cons (.inr .rax) (-1 : Int) $
  .cons (.inr .rsp) (-2 : Int) $
  .cons (.inr .rbp) (-3 : Int) $
  .cons (.inr .r11) (-4 : Int) $
  .cons (.inr .r15) (-5 : Int) $
  .nil

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
countUnique {α : Type} [BEq α] : List α → List α → Nat
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

private def block : x86_Var.Block := 
  .block { live_before := .none } [
  .movq (.imm 1) (.var (.quote "v")),
  .movq (.imm 42) (.var (.quote "w")),
  .movq (.var (.quote "v")) (.var (.quote "x")),
  .addq (.imm 7) (.var (.quote "x")),
  .movq (.var (.quote "x")) (.var (.quote "y")),
  .movq (.var (.quote "x")) (.var (.quote "z")),
  .addq (.var (.quote "w")) (.var (.quote "z")),
  .movq (.var (.quote "y")) (.var (.quote "t")),
  .negq (.var (.quote "t")),
  .movq (.var (.quote "z")) (.reg .rax),
  .addq (.var (.quote "t")) (.reg .rax),
  .jmp "conclusion"
  ]

private def verticies : List (Sym⊕ Reg) := [
    (.inl $ .quote "t"),
    (.inl $ .quote "v"),
    (.inl $ .quote "w"),
    (.inl $ .quote "x"),
    (.inl $ .quote "y"),
    (.inl $ .quote "z")
  ]

#eval 
  match x86_Var.uncover_live block with 
  | .block info _ => info.live_before

#eval x86_Var.interference_for_block $ x86_Var.uncover_live $ block

#eval 
  let graph := x86_Var.interference_for_block $ x86_Var.uncover_live $ block
  (x86_Var.graph_to_coloring graph verticies).toList
