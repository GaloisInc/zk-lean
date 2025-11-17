import Init.Data.Array.Basic
import Init.Data.Array.Set
import Init.Prelude
import Mathlib.Algebra.Field.Defs

import ZKLean.AST
import ZKLean.Builder
import ZKLean.SimpSets

/-- Class for Fields with additional properties necessary for ZKLean -/
class ZKField (f: Type) extends Field f, BEq f, Inhabited f, LawfulBEq f, Hashable f where
  -- Mask the lower `num_bits` of a field element and convert to a vector of bits.
  field_to_bits {num_bits: Nat} (val: f) : Vector f num_bits
  field_to_nat (val: f) : Nat

structure RamState f [ZKField f] where
  capacity: ℕ
  state: (Std.HashMap f f)

abbrev RamStates f [ZKField f] := Array (RamState f)

structure ZKState (f : Type) [ZKField f] where
  allocated_witness_count: Nat
  witness: Array f
  rams: RamStates f
  -- -- Pairs of expressions that are constrained to be equal to one another.
  -- constraints: List (ZKExpr f × ZKExpr f)
  -- -- Array of sizes and array of operations for each RAM.
  -- ram_sizes: Array Nat
  -- ram_ops: (Array (RamOp f))
deriving instance Inhabited for ZKBuilderState

@[simp_ZKBuilder]
def ZKState.eval_expr [ZKField f] (st: ZKState f) (e: ZKExpr f) : Option f := 
  match e with
    | ZKExpr.Field f => f
    | ZKExpr.WitnessVar id => panic! "TODO"
    | ZKExpr.Add lhs rhs => do
        pure ((← st.eval_expr lhs) + (← st.eval_expr rhs))
    | ZKExpr.Sub lhs rhs => do
        pure ((← st.eval_expr lhs) - (← st.eval_expr rhs))
    | ZKExpr.Mul lhs rhs => do
        pure ((← st.eval_expr lhs) * (← st.eval_expr rhs))
    | ZKExpr.Neg arg => do
        pure (-(← st.eval_expr arg))
    | ZKExpr.ComposedLookupMLE table c0 c1 c2 c3 => do
      let chunks := #v[← st.eval_expr c0, ← st.eval_expr c1, ← st.eval_expr c2, ← st.eval_expr c3].map ZKField.field_to_bits
      pure (evalComposedLookupTable table chunks)
    | ZKExpr.LookupMLE table e1 e2 => do
        pure (evalLookupTableMLE table
          (ZKField.field_to_bits (num_bits := 32) (← st.eval_expr e1))
          (ZKField.field_to_bits (num_bits := 32) (← st.eval_expr e2)))
    | ZKExpr.LookupMaterialized table e => do
      table[ZKField.field_to_nat (← st.eval_expr e)]?
    | ZKExpr.RamOp op_id => panic! "TODO"


/-- Interprets a ZK operation give a state. On success, it returns the result of the operation and the updated state. If a constraint in the circuit is not satisfied, it short circuits and returns `.none`. -/
@[simp_ZKBuilder]
def ZKOpInterp [ZKField f] {β} (op : ZKOp f β) (st : ZKState f) : Option (β × ZKState f) :=
  match op with
  | ZKOp.AllocWitness => do
      let idx := st.allocated_witness_count
      .some (ZKExpr.Field (<- st.witness[idx]?), { st with allocated_witness_count := idx + 1 })
  | ZKOp.ConstrainEq x y => do
      let fx ← st.eval_expr x
      let fy ← st.eval_expr y
      if fx == fy then
        .some ((), st)
      else
        .none
  | ZKOp.ConstrainR1CS a b c => do
      let fa ← st.eval_expr a
      let fb ← st.eval_expr b
      let fc ← st.eval_expr c
      if fa * fb == fc then
        .some ((), st)
      else
        .none
  | ZKOp.ComposedLookupMLE tbl args =>
      (ZKExpr.ComposedLookupMLE tbl args[0] args[1] args[2] args[3], st)
  | ZKOp.LookupMLE tbl arg1 arg2 =>
      (ZKExpr.LookupMLE tbl arg1 arg2, st)
  | ZKOp.LookupMaterialized tbl arg =>
      (ZKExpr.LookupMaterialized tbl arg, st)
  | ZKOp.MuxLookup ch cases =>
      let sum := Array.foldl (fun acc (flag, tbl) =>
        acc + ZKExpr.Mul flag (ZKExpr.ComposedLookupMLE tbl ch[0] ch[1] ch[2] ch[3])) (ZKExpr.Field (0 : f)) cases
      (sum, st)
  | ZKOp.RamNew n =>
      let id := st.rams.size
      let state := { capacity:= n, state:= Std.HashMap.emptyWithCapacity n }
      pure ({id := { ram_id := id}}, {st with rams := st.rams.push state})
  | ZKOp.RamRead ram_id a => do
      let addr_f ← st.eval_expr a
      let ram ← st.rams[ram_id.id.ram_id]?
      let val ← ram.state[addr_f]?
      pure (ZKExpr.Field val, st)
  | ZKOp.RamWrite ram_id a v => do
      let addr_f ← st.eval_expr a
      let val_f ← st.eval_expr v
      if h:ram_id.id.ram_id < st.rams.size then
        let ram := st.rams[ram_id.id.ram_id]
        let new_ram := {ram with state := ram.state.insert addr_f val_f}
        let new_rams := st.rams.set ram_id.id.ram_id new_ram
        pure ((), {st with rams := new_rams})
      else
        .none


@[simp_ZKBuilder]
def runFold [ZKField f] (p : ZKBuilder f α) (st : ZKState f)
    : Option (α × ZKState f) :=
  FreeM.foldM
    -- pure case : just return the value, leaving the state untouched
    (fun a => fun st => .some (a, st))
    -- bind case : interpret one primitive with `ZKOpInterp`, then feed the
    -- resulting value into the continuation on the updated state.
    (fun op k => fun st => do
      let (b, st') <- ZKOpInterp op st
      k b st')
    p st






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
    | ZKExpr.Field lit => some lit
    | ZKExpr.WitnessVar id => witness[id]?
    | ZKExpr.Add lhs rhs => do (← eval lhs) + (← eval rhs)
    | ZKExpr.Sub lhs rhs => do (← eval lhs) - (← eval rhs)
    | ZKExpr.Mul lhs rhs => do (← eval lhs) * (← eval rhs)
    | ZKExpr.Neg arg => do some (- (← eval arg))
    | ZKExpr.ComposedLookupMLE table c0 c1 c2 c3 => do
      let chunks := #v[← eval c0, ← eval c1, ← eval c2, ← eval c3].map ZKField.field_to_bits
      some (evalComposedLookupTable table chunks)
    | ZKExpr.LookupMLE table e1 e2 =>
      do
        some (evalLookupTableMLE table
          (ZKField.field_to_bits (num_bits := 32) (← eval e1))
          (ZKField.field_to_bits (num_bits := 32) (← eval e2)))
    | ZKExpr.LookupMaterialized table e =>
      do table[ZKField.field_to_nat (← eval e)]?
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
def semantics_old [ZKField f] (witness: List f) (state: ZKBuilderState f) : Bool :=
  -- First, we need to evaluate the RAM operations and get the values
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops;
  -- Then, we need to evaluate the constraints
  if let some ram_values := ram_values
  then semantics_constraints state.constraints witness ram_values
  else
    -- If the RAM values are not valid, we return
    false

@[simp_ZKSemantics]
def semantics [ZKField f] (circuit: ZKBuilder f α) (witness: List f) : Bool :=
  let st : ZKState f := {witness := witness.toArray, allocated_witness_count := 0, rams:= Array.empty}
  let res := runFold circuit st
  res.isSome
