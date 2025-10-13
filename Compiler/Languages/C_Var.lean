import Compiler.Data.Sym
import Lean.Data

inductive C_Var.Label where
  | label : String → Label
  deriving Repr

inductive C_Var.Atom where
  | var : Sym → Atom
  | int : Int → Atom
  deriving Repr, BEq

inductive C_Var.Expr where
  | atom : Atom → Expr
  | plus : Atom → Atom → Expr
  | minus : Atom → Atom → Expr
  | negative : Atom → Expr
  | read : Expr
  deriving Repr

inductive C_Var.Stmt where
  | assign : Sym → Expr → Stmt
  deriving Repr

inductive C_Var.Tail where
  | ret : Expr → Tail
  | seq : Stmt → Tail → Tail
  deriving Repr

structure C_Var.Info where
  locals_types : Lean.AssocList Sym Sym

inductive C_Var.Program where
  | program : Info → List (Label × Tail) → Program

def C_Var.Program.mk : List (Label × Tail) → Program
| ls => program { locals_types := get_info ls } ls
where 
  tail_locals : Tail → List (Sym × Sym)
  | .ret _ => .nil -- ret doesn't assign
  | .seq (.assign v _) rest => (v, (.quote "Integer")) :: (tail_locals rest)
  get_info : List (Label × Tail) → Lean.AssocList Sym Sym
  | ls => (ls.foldl (fun acc (_, tail) => tail_locals tail ++ acc) []).toAssocList'
