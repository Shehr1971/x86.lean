import Compiler

unsafe def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let program ← IO.FS.Stream.readToEnd stdin
  let mrslt ← match L_Var.Expr.parse_expr program.iter with
    | .success _ expr => pure $ x86_Int.Program.prelude_and_conclusion
    <$> x86_Int.Program.patch_instructions
    <$> (x86_Var.Program.assign_homes
        $ x86_Var.Program.build_interference
        $ x86_Var.Program.uncover_live
        $ x86_Var.from_C_Var
        $ (fun tail => C_Var.Program.mk [("start", tail)])
        $ C_Var.explicate_control
        $ L_Var.remove_complex_operands expr)
    | .error _ s => throw $ IO.Error.mkInvalidArgument 1 s!"Couldn't parse: {s}"
  match mrslt with
  | .none => throw $ IO.Error.mkInvalidArgument 1 s!"Couldn't find homes for variables!"
  | .some rslt => do
    stdout.putStrLn ".globl main"
    stdout.putStr s!"{rslt}"
