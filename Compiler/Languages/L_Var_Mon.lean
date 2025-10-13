import Compiler.Data.Sym

inductive L_Var_Mon.Atom
| int : Int → Atom
| var : Sym → Atom
deriving Repr

inductive L_Var_Mon.Expr
| plus : Atom → Atom → Expr
| minus : Atom → Atom → Expr
| negative : Atom → Expr
| let : Sym → Expr → Expr → Expr
| atom : Atom → Expr
| read : Expr
deriving Repr
