inductive Reg
| rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi 
| r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
deriving BEq

instance instToStringLabel_x86_Reg : ToString Reg where
  toString : Reg → String
  | .rsp => "%rsp"
  | .rbp => "%rbp"
  | .rax => "%rax"
  | .rbx => "%rbx"
  | .rcx => "%rcx"
  | .rdx => "%rdx"
  | .rsi => "%rsi"
  | .rdi => "%rdi"
  | .r8  => "%r8"
  | .r9  => "%r9"
  | .r10 => "%r10"
  | .r11 => "%r11"
  | .r12 => "%r12"
  | .r13 => "%r13"
  | .r14 => "%r14"
  | .r15 => "%r15"

macro:max "%" ident:ident : term => do
  pure $ Lean.mkIdent $ Lean.Name.mkStr `Reg ident.getId.toString
