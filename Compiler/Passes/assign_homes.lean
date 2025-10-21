import Compiler.Passes.select_instructions
import Compiler.Languages.x86_Int

def x86_Var.Arg.assign_homes : Lean.AssocList Sym Nat → x86_Var.Arg → Option x86_Int.Arg
| _, .imm i => pure $ .imm i
| _, .reg r => pure $ .reg r
| _, .deref r i => pure $ .deref r i
| l, .var s => match l.find? s with
  | .some i => pure $ x86_Int.Arg.deref .rbp ((i : Int) * -8)
  | .none => .none

def x86_Var.Instr.assign_homes : Lean.AssocList Sym Nat → x86_Var.Instr → Option x86_Int.Instr
| l, .addq a b => .addq <$> Arg.assign_homes l a <*> Arg.assign_homes l b
| l, .subq a b => .subq <$> Arg.assign_homes l a <*> Arg.assign_homes l b
| l, .negq a => .negq <$> Arg.assign_homes l a
| l, .pushq a => .pushq <$> Arg.assign_homes l a
| l, .popq a => .popq <$> Arg.assign_homes l a
| l, .movq a b => .movq <$> Arg.assign_homes l a <*> Arg.assign_homes l b
| _, .callq l n => pure $ .callq l n
| _, .jmp l => pure $ .jmp l 
| _, .retq => pure $ .retq

def x86_Var.Block.assign_homes : Lean.AssocList Sym Nat → x86_Var.Block → Option x86_Int.Block
| l, .block _ instrs => .block <$> instrs.mapM (fun i => Instr.assign_homes l i)

def x86_Var.Program.assign_homes : x86_Var.Program → Option x86_Int.Program
| .program info blocks => .program 
  { locals_types := info.locals_types, stack_space := info.stack_space }
  <$> blocks.mapM (redoBlock info)
where 
locations_for_locals : Lean.AssocList Sym Sym → Lean.AssocList Sym Nat
| locals => (locals.toList.foldr (fun (v,_) (l,n)  => (l.insert v n, n+1)) (.nil, 1)).1
redoBlock : PInfo → (Label × Block) → Option (Label×x86_Int.Block)
| info, (l, b) => (.,.) <$> pure l <*> Block.assign_homes (locations_for_locals info.locals_types) b

#eval match L_Var.Expr.parse_expr "(let 'x (read) (+ (- 'x 1) 'x))".iter with
  | .success _ expr => x86_Var.Program.assign_homes
  $ x86_Var.from_C_Var
  $ (fun tail => C_Var.Program.mk [("start", tail)])
  $ C_Var.explicate_control
  $ L_Var.remove_complex_operands expr
  | .error _ _ => Option.none
