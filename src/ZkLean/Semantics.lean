import Init.Data.Array.Basic
import Init.Data.Array.Set
import Init.Prelude
import Mathlib.Algebra.Field.Defs

import ZkLean.AST
import ZkLean.Builder
import ZkLean.SimpSets

/-- Class for Fields with additional properties necessary for ZkLean -/
class ZKField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f, Hashable f where
  -- Mask the lower `num_bits` of a field element and convert to a vector of bits.
  field_to_bits {num_bits: Nat} (val: f) : Vector f num_bits
  field_to_nat (val: f) : Nat


/-- Type for the evaluation of RAM operations

It is an array of options, where each option is either some value when it is the result of a read operation,
or none when it is the result of a write operation.
-/
abbrev RamOpsEval f [ZKField f] := Array (Option f)

/-- Semantics for `ZKExpr`

The semantics of the ZKExpr is defined as a recursive function that takes a `ZKExpr`,
a witness vector, some RAM values, and returns an a field value when the expression
evaluates correctly or nothing if the expression is not well defined.
-/
@[simp_ZKSemantics]
def semantics_zkexpr [ZKField f]
  (expr: ZKExpr f)
  (witness: List f)
  (ram_values: RamOpsEval f)
  : Option f :=
  let rec @[simp_ZKSemantics] eval (e: ZKExpr f) : Option f :=
    match e with
    | ZKExpr.Literal lit => some lit
    | ZKExpr.WitnessVar id => witness[id]?
    | ZKExpr.Add lhs rhs => do (← eval lhs) + (← eval rhs)
    | ZKExpr.Sub lhs rhs => do (← eval lhs) - (← eval rhs)
    | ZKExpr.Mul lhs rhs => do (← eval lhs) * (← eval rhs)
    | ZKExpr.Neg arg => do some (- (← eval arg))
    | ZKExpr.ComposedLookup table c0 c1 c2 c3 => do
      let chunks := #v[← eval c0, ← eval c1, ← eval c2, ← eval c3].map ZKField.field_to_bits
      some (evalComposedLookupTable table chunks)
    | ZKExpr.LookupMLE table e1 e2 =>
      match (eval e1, eval e2) with
      | (some v1, some v2) =>
        some (evalLookupTableMLE table
          (ZKField.field_to_bits (num_bits := 32) v1)
          (ZKField.field_to_bits (num_bits := 32) v2))
      | _ => none
    | ZKExpr.LookupMaterialized table e =>
      let ev := eval e
      match ev with
      | (some v0) =>
        let idx := ZKField.field_to_nat v0
        table[idx]?
      | _ => none
    | ZKExpr.RamOp op_id =>
      if let some opt := ram_values[op_id]?
      then opt
      else none

  eval expr



/-- A type capturing the state of the RAM

It is a mapping between the RAM id and the values stored in the RAM.
The values are stored in a hash map, where the keys are the addresses and the values are the field values.
-/
abbrev RamEnv f [ZKField f] := Array (Std.HashMap f f)


/-- Semantics for RAM operations

Execute all the rams operations sequentially, maintain a mapping between addresses and values.
This mapping is used to read or write values to the RAM.
-/
def semantics_ram [ZKField f]
  (witness: List f)
  (ram_sizes: Array Nat)
  (ram_ops: Array (RamOp f))
  : Option (RamOpsEval f) := do
  -- Let's create the empty environment
  let empty_env: RamEnv f := Array.mkArray ram_sizes.size (Std.HashMap.empty);

  -- For every RAM operation, update the RAM environment and the list of evaluated operations
  let res <- Array.foldlM  (λ (env, ops_eval) ram_op =>
    match ram_op with
    | RamOp.Read ram_id addr => do
      let addr_f <- semantics_zkexpr addr witness ops_eval;
      let ram <- env[ram_id.ram_id]?;
      let val <- ram[addr_f]?;
      let new_ops_eval := Array.push ops_eval (some val);
        pure (env, new_ops_eval)
    | RamOp.Write ram_id addr val => do
      let addr_f <- semantics_zkexpr addr witness ops_eval;
      let val_f  <- semantics_zkexpr val witness ops_eval;
      let ram <- env[ram_id.ram_id]?;
      let new_ram := ram.insert addr_f val_f
      let new_ops_eval := Array.push ops_eval (none);
      if h: ram_id.ram_id >= env.size
      then none
      else
      let (_, new_env) := env.swapAt ram_id.ram_id new_ram;
      pure (new_env, new_ops_eval)

  ) (empty_env, Array.empty) ram_ops -- TODO: Array.emptyWithCapacity

  -- return the list of evaluated RAM operations
  pure res.2

/-- Semantics for equality constraints

It takes a list of constraints, a list of witnesses and a list of RAM operation values
-/
@[simp_ZKSemantics]
def semantics_constraints [ZKField f]
  (constraints: List (ZKExpr f × ZKExpr f))
  (witness: List f)
  (ram_values: RamOpsEval f)
  : Bool :=
  match constraints with
  | [] => true
  | (c, d) :: cs =>
    let sem_c := semantics_zkexpr c witness ram_values
    let sem_d := semantics_zkexpr d witness ram_values
    match sem_c, sem_d with
    | some cf, some df =>
      if cf == df
      then semantics_constraints cs witness ram_values
      else false
    | _, _ => false


/-- Main semantics function

It takes a list of witnesses and a state of constructed ZK circuit and returns a boolean indicating
whether the circuit is satisfied.
-/
@[simp_ZKSemantics]
def semantics [ZKField f] (witness: List f) (state: ZKBuilderState f) : Bool :=
  -- First, we need to evaluate the RAM operations and get the values
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops;
  -- Then, we need to evaluate the constraints
  if let some ram_values := ram_values
  then semantics_constraints state.constraints witness ram_values
  else
    -- If the RAM values are not valid, we return
    false
