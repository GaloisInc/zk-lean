import Mathlib.Algebra.Field.Defs
import ZkLean.AST
import ZkLean.Builder
import Init.Prelude
import Init.Data.Array.Basic
import Init.Data.Array.Set

/-- Class for Fields with additional properties necessary for ZkLean -/
class ZKField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f, Hashable f where
  -- Mask the lower `num_bits` of a field element and convert to a vector of bits.
  chunk_to_bits {num_bits: Nat} (val: f) : Vector f num_bits


-- TODO: Isn't this redundant with `Witnessable f (ZKExpr f)` in Builder.lean?
instance [ZKField f]: Witnessable f (ZKExpr f) where
  witness := witnessf


/-- Type for the evaluation of RAM operations

It is an array of options, where each option is either some value when it is the result of a read operation, and none when it is the result of a write operation.
-/
abbrev RamOpsEval f [ZKField f] := Array (Option f)

/-- Semantics for `ZKExpr`

The semantics of the ZKExpr is defined as a recursive function that takes a `ZKExpr`,
a witness vector, some RAM values, and returns an a field value when the expression
evaluates correctly or nothing if the expression is not well defined.
-/
def semantics_zkexpr [ZKField f]
  (expr: ZKExpr f)
  (witness: List f )
  (ram_values: RamOpsEval f)
  : Option f :=
  let rec eval (e: ZKExpr f) : Option f :=
    match e with
    | ZKExpr.Literal lit => some lit
    | ZKExpr.WitnessVar id =>
      if let some v := witness[id]?
      then some v
      else none
    | ZKExpr.Add lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | some va, some vb => some (va + vb)
      | _, _ => none
    | ZKExpr.Sub lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | some va, some vb => some (va - vb)
      | _, _ => none
    | ZKExpr.Neg rhs =>
      let a := eval rhs
      match a with
      | some va => some (-va)
      | _ => none
    | ZKExpr.Mul lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | some va, some vb => some (va * vb)
      | _, _ => none
    | ZKExpr.Lookup table c0 c1 c2 c3 =>
      let e0 := eval c0
      let e1 := eval c1
      let e2 := eval c2
      let e3 := eval c3
      match (e0, e1, e2, e3) with
      | (some v0, some v1, some v2, some v3) =>
        let chunks := Vector.map (λ f => ZKField.chunk_to_bits f) #v[v0, v1, v2, v3]
        some (evalComposedLookupTable table chunks)
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

  -- call the function `semantics_zkexpr` and extract the field value in an option
  let semantics_zkexpr_f expr witness ops_eval :=
    let x := semantics_zkexpr expr witness ops_eval;
    match x with
    | some n => some n
    | _ => none

  -- For every RAM operation, update the RAM environment and the list of evaluated operations
  let res <- Array.foldlM  (λ (env, ops_eval) ram_op =>
    match ram_op with
    | RamOp.Read ram_id addr => do
      let addr_f <- semantics_zkexpr_f addr witness ops_eval;
      let ram <- env[ram_id.ram_id]?;
      let val <- ram[addr_f]?;
      let new_ops_eval := Array.push ops_eval (some val);
        pure (env, new_ops_eval)
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

  -- return the list of evaluated RAM operations
  pure res.2

/-- Semantics for equality constraints

It takes a list of constraints, a list of witnesses and a list of RAM operation values
-/
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
def semantics [ZKField f] (witness: List f) (state: ZKBuilderState f) : Bool :=
  -- First, we need to evaluate the RAM operations and get the values
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops;
  -- Then, we need to evaluate the constraints
  if let some ram_values := ram_values
  then semantics_constraints state.constraints witness ram_values
  else
    -- If the RAM values are not valid, we return
    false
