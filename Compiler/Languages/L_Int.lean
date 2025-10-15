import Std.Internal.Parsec

inductive L_Int_Expr
| plus : L_Int_Expr → L_Int_Expr → L_Int_Expr
| minus : L_Int_Expr → L_Int_Expr → L_Int_Expr
| negative : L_Int_Expr → L_Int_Expr
| read : L_Int_Expr
| int : Int → L_Int_Expr
deriving Repr

inductive L_Int_Program
| Program : L_Int_Expr → L_Int_Program

open Std.Internal
open Parsec.String
open Std.Internal.Parsec

def L_Int_Expr.parse_atom : Parsec String.Iterator L_Int_Expr := do
  let minus ← optional (pchar '-')
  let digits ← digits
  let int : Int := digits
  match minus with
  | .some _ => pure $ L_Int_Expr.int (int * -1)
  | .none => pure $ L_Int_Expr.int int

mutual

unsafe def L_Int_Expr.parse_complex : Parsec String.Iterator L_Int_Expr :=
  pchar '(' *> ws *> parse_inner <* ws <* pchar ')'

unsafe def L_Int_Expr.parse_plus : Parsec String.Iterator L_Int_Expr :=
  plus <$> (pchar '+' *> ws *> parse_expr) <*> (ws *> parse_expr)
  
unsafe def L_Int_Expr.parse_minus : Parsec String.Iterator L_Int_Expr :=
  minus <$> (pchar '-' *> ws *> parse_expr) <*> (ws *> parse_expr)

unsafe def L_Int_Expr.parse_negative : Parsec String.Iterator L_Int_Expr := 
  negative <$> (pstring "-" *> ws *> parse_expr)

unsafe def L_Int_Expr.parse_read : Parsec String.Iterator L_Int_Expr := 
  pstring "read" *> pure read

unsafe def L_Int_Expr.parse_inner : Parsec String.Iterator L_Int_Expr := 
  parse_plus <|> parse_read <|> attempt parse_minus <|> parse_negative

unsafe def L_Int_Expr.parse_expr : Parsec String.Iterator L_Int_Expr :=
  parse_atom <|> parse_complex 

end

def L_Int_Expr.eval_expr : L_Int_Expr → IO Int 
| .plus a b => (. + .) <$> eval_expr a <*> eval_expr b
| .minus a b => (. - .) <$> eval_expr a <*> eval_expr b
| .negative a => (. * -1) <$> eval_expr a
| .int a => pure a
| .read => IO.getStdin >>= IO.FS.Stream.getLine >>= pure ∘ parseDigits
where parseDigits s := match Parser.run digits s with | .ok n => n | _ => 0

unsafe def L_Int_Expr.eval_str (s : String) : IO Int :=
  match parse_expr s.iter with
  | .success _ res => eval_expr res
  | .error _ _ => MonadExceptOf.throw $ IO.userError "Couldn't Parse String"
