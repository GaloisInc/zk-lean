import Mathlib.Algebra.Field.Defs
import ZkLean.AST
import ZkLean.Builder
import Init.Prelude
import Init.Data.Array.Basic
import Init.Data.Array.Set

class JoltField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f, Hashable f where
  -- Mask the lower `num_bits` of a field element and convert to a vector of bits.
  chunk_to_bits {num_bits: Nat} (val: f) : Vector f num_bits

instance [JoltField f]: Witnessable f (ZKExpr f) where
  witness := witnessf


-- The semantics associated with the ZKExpr will return either a field value or a boolean value, and none if the expression is not well defined.
inductive Value (f: Type) [JoltField f] where
  | VBool : Bool -> Value f
  | VField : f -> Value f
  | None : Value f

-- A type for the evaluation of the RAM operations
-- It is an array of options, where each option is either some value when it is the result of a read operation, and none when it is the result of a write operation.
abbrev RamOpsEval f [JoltField f] := Array (Option f)

-- The semantics of the ZKExpr is defined as a recursive function that takes a ZKExpr, a witness vector and a RAM
def semantics_zkexpr [JoltField f]
  (expr: ZKExpr f)
  (witness: List f )
  (ram_values: RamOpsEval f)
  : Value f :=
  let rec eval (e: ZKExpr f) : Value f :=
    match e with
    | ZKExpr.Literal lit => Value.VField lit
    | ZKExpr.WitnessVar id =>
      if let some v := witness[id]?
      then Value.VField v
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
    | ZKExpr.Lookup table c0 c1 c2 c3 =>
      let e0 := eval c0
      let e1 := eval c1
      let e2 := eval c2
      let e3 := eval c3
      match (e0,e1,e2,e3) with
      | (Value.VField v0, Value.VField v1, Value.VField v2, Value.VField v3) =>
        -- let h : Even 16 := by
        --   exact (Even.add_self 8)
        -- OLD: Value.VField (evalComposedLookupTableArgs h table va vb)
        let chunks := Vector.map (λ f => JoltField.chunk_to_bits f) #v[v0, v1, v2, v3]
        Value.VField (evalComposedLookupTable table chunks)
      | _ => Value.None
    | ZKExpr.RamOp op_id =>
      if let some opt := ram_values[op_id]?
      then if let some f := opt
           then Value.VField f
           else Value.None
      else Value.None


  eval expr


-- A type capturing the state of the RAM
-- It is a mapping between the RAM id and the values stored in the RAM.
-- The values are stored in a hash map, where the keys are the addresses and the values are the field values.
abbrev RamEnv f [JoltField f] := Array (Std.HashMap f f)


-- Execute all the rams operations sequentially, maintain a mapping between addresses and values.
-- This mapping is used to read or write values to the RAM.
def semantics_ram [JoltField f]
  (witness: List f)
  (ram_sizes : Array Nat)
  (ram_ops: Array (RamOp f))
  : Option (RamOpsEval f) := do
  -- Let's create the empty environment
  let empty_env: RamEnv f := Array.mkArray ram_sizes.size (Std.HashMap.empty);

  -- call the function `semantics_zkexpr` and extract the field value in an option
  let semantics_zkexpr_f expr witness ops_eval :=
    let x := semantics_zkexpr expr witness ops_eval;
    match x with
    | Value.VField n => some n
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

-- (Generate a comment that says that this function is the semantics of the constraints and take some witness and ram values)
-- Function for the semantics of the constraints
-- It takes a list of constraints and a list of witnesses and a list of RAM operation values
def semantics_constraints [JoltField f] (constraints: List (ZKExpr f × ZKExpr f)) (witness: List f ) (ram_values: RamOpsEval f): Bool :=
  match constraints with
  | [] => true
  | (c, d) :: cs =>
    let sem_c := semantics_zkexpr c witness ram_values
    let sem_d := semantics_zkexpr d witness ram_values
    match sem_c, sem_d with
    | Value.VField cf, Value.VField df =>
      if cf == df
      then semantics_constraints cs witness ram_values
      else false
    | _, _ => false


-- This function is the main semantics function, it takes a list of witnesses and
-- a state of constructed ZK circuit and returns a boolean indicating whether the circuit is satisfied.
def semantics [JoltField f] (witness: List f ) (state: ZKBuilderState f) : Bool :=
  -- First, we need to evaluate the RAM operations and get the values
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops;
  -- Then, we need to evaluate the constraints
  if let some ram_values := ram_values
  then semantics_constraints state.constraints witness ram_values
  else
    -- If the RAM values are not valid, we return
    false
