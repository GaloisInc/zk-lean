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
deriving instance Inhabited for ZKState

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







/-- Main semantics function

It takes a ZK circuit and list of witnesses and returns a boolean indicating
whether the circuit is satisfied.
-/
@[simp_ZKSemantics]
def semantics [ZKField f] (circuit: ZKBuilder f α) (witness: List f) : Bool :=
  let st : ZKState f := {witness := witness.toArray, allocated_witness_count := 0, rams:= Array.empty}
  let res := runFold circuit st
  res.isSome
