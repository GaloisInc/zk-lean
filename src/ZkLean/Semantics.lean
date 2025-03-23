import Mathlib.Algebra.Field.Defs
import ZkLean.AST
import ZkLean.Builder

class JoltField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f

instance [JoltField f]: Witnessable f (ZKExpr f) where
  witness := witnessf

inductive Value (f: Type) [JoltField f] where
  | VBool : Bool -> Value f
  | VField : f -> Value f
  | None : Value f

def semantics_zkexpr [JoltField f] (exprs: ZKExpr f) (witness: List f ) : Value f :=
  let rec eval (e: ZKExpr f) : Value f :=
    match e with
    | ZKExpr.Literal lit => Value.VField lit
    | ZKExpr.WitnessVar id =>
      if compare id (witness.length : WitnessId) == Ordering.lt
      then Value.VField (witness.get! id)
      else Value.None
    | ZKExpr.Add lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va + vb)
      | _, _ => Value.None
    | ZKExpr.Sub lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va - vb)
      | _, _ => Value.None
    | ZKExpr.Neg rhs =>
      let a := eval rhs
      match a with
      | Value.VField va => Value.VField (-va)
      | _ => Value.None
    | ZKExpr.Mul lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va * vb)
      | _, _ => Value.None
    | ZKExpr.Eq lhs rhs  =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb =>
        let b: Bool := va == vb
        Value.VBool b
      | _, _ => Value.None
    | ZKExpr.Lookup table arg1 arg2 =>
      let a := eval arg1
      let b := eval arg2
      match a,b with
      | Value.VField va, Value.VField vb =>
        let h : Even 16 := by
          exact (Even.add_self 8)
        Value.VField (evalComposedLookupTableArgs h table va vb)
      | _, _ => Value.None
  eval exprs

def constraints_semantics [JoltField f] (constraints: List (ZKExpr f)) (witness: List f ) : Bool :=
  match constraints with
  | [] => true
  | c :: cs =>
    let sem_c := semantics_zkexpr c witness
    match sem_c with
    | Value.VBool b =>
      if b
      then constraints_semantics cs witness
      else false
    | _ => false
