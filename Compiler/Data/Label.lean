inductive Label
| label : String → Label

instance : ToString Label where
  toString : Label → String
  | .label s => s

instance : Coe String Label where
  coe s := .label s
