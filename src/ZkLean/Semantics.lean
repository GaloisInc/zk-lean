import Mathlib.Algebra.Field.Defs
import ZkLean.AST
import ZkLean.Builder
import Init.Prelude
import Init.Data.Array.Basic
import Init.Data.Array.Set

class JoltField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f, Hashable f

instance [JoltField f]: Witnessable f (ZKExpr f) where
  witness := witnessf

inductive Value (f: Type) [JoltField f] where
  | VBool : Bool -> Value f
  | VField : f -> Value f
  | None : Value f


def semantics_zkexpr [JoltField f]
  (expr: ZKExpr f)
  (witness: List f )
  (ram_values: Array (Option f))
  : Value f :=
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
    | ZKExpr.RamOp op_id =>
      let x: _ := ram_values.get op_id ;
      if let some opt := ram_values.get? op_id
      then if let some f := opt
           then Value.VField f
           else Value.None
      else Value.None


  eval expr


abbrev RamEnv f [JoltField f] := Array (Std.HashMap f f)

-- Execute all the rams operations sequentially, maintain a mapping between addresses and values.
-- This mapping is used to read or write values to the RAM.
def semantics_ram [JoltField f]
  (witness: List f)
  (ram_sizes : Array Nat)
  (ram_ops: Array (RamOp f))
  : Option (Array (Option f)) := do
  -- Let's create the empty environment
  let empty_env: RamEnv f := Array.mkArray ram_sizes.size (Std.HashMap.empty);

  let semantics_zkexpr_f addr witness ops_eval :=
    let x := semantics_zkexpr addr witness ops_eval;
    match x with
    | Value.VField n => some n
    | _ => none

  let res <- Array.foldlM  (λ (env, ops_eval) ram_op =>
    match ram_op with
    | RamOp.Read ram_id addr =>
      let addr_f := semantics_zkexpr addr witness ops_eval;
      match addr_f with
      | Value.VField n =>
        do
        let ram <- env[ram_id.ram_id]?;
        let val <- ram[n]?;
        let new_ops_eval := Array.push ops_eval (some val);
        pure (env, new_ops_eval)
      | _ => none
    | RamOp.Write ram_id addr val => do
      let addr_f <- semantics_zkexpr_f addr witness ops_eval;
      let val_f  <- semantics_zkexpr_f val witness ops_eval;
      let ram <- env[ram_id.ram_id]?;
      let new_ram := ram.insert addr_f val_f
      let new_ops_eval := Array.push ops_eval (none);
      if h: ram_id.ram_id >= env.size
      then none
      else
      let (_, new_env) := env.swapAt ram_id.ram_id new_ram;
      pure (new_env, new_ops_eval)

  ) (empty_env, Array.empty) ram_ops -- TODO: Array.emptyWithCapacity
  pure res.2



def constraints_semantics [JoltField f] (constraints: List (ZKExpr f)) (witness: List f ) (ram_values: Array (Option f)): Bool :=
  match constraints with
  | [] => true
  | c :: cs =>
    let sem_c := semantics_zkexpr c witness ram_values
    match sem_c with
    | Value.VBool b =>
      if b
      then constraints_semantics cs witness ram_values
      else false
    | _ => false

def semantics [JoltField f] (witness: List f ) (state: ZKBuilderState f) : Bool :=
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops;
  if let some ram_values := ram_values
  then constraints_semantics state.constraints witness ram_values
  else false
