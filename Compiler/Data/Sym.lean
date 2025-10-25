inductive Sym
| quote : String → Sym
deriving Repr, BEq, DecidableEq

instance : LawfulBEq Sym where
  eq_of_beq { a b } h := by
    cases a with | quote s1 =>
    cases b with | quote s2 =>
    have : s1 = s2 := LawfulBEq.eq_of_beq h
    simp_all

  rfl { a } := by
    cases a with | quote s => 
    simp only [show (Sym.quote s == Sym.quote s) = (s == s) by rfl]
    simp

instance : ToString Sym where
  toString : Sym → String
  | .quote x => s!"&{x}"

-- Define the macro that transforms 'ident into .symbol "ident"
macro:max "&" ident:ident : term =>
  `(Sym.quote $(Lean.Syntax.mkStrLit ident.getId.toString))
