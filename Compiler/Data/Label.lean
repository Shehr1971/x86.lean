inductive Label
| label : String → Label

instance : ToString Label where
  toString : Label → String
  | .label s => s
