import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable
import ZkLean.FreeMonad
import Std.Do
import Std.Tactic.Do

/-- Type for RAM operations (Read and Write) -/
inductive RamOp (f : Type) where
  | Read  (ram_id: RamId) (addr: ZKExpr f)
  | Write (ram_id: RamId) (addr: ZKExpr f) (value: ZKExpr f)
deriving instance Inhabited for RamOp

/--
State associated with the building process of a ZK circuit.

It holds witnesses, constraints, and RAM operations.
-/
structure ZKBuilderState (f : Type) where
  allocated_witness_count: Nat
  -- Pairs of expressions that are constrained to be equal to one another.
  constraints: List (ZKExpr f × ZKExpr f)
  -- Array of sizes and array of operations for each RAM.
  ram_sizes: Array Nat
  ram_ops: (Array (RamOp f))
deriving instance Inhabited for ZKBuilderState

/-- Primitive instructions for the circuit DSL - the effect 'functor'. -/
inductive ZKOp (f : Type) : Type → Type
| AllocWitness                         : ZKOp f (ZKExpr f)
| ConstrainEq    (x y    : ZKExpr f)   : ZKOp f PUnit
| ConstrainR1CS  (a b c  : ZKExpr f)   : ZKOp f PUnit
| Lookup         (tbl    : ComposedLookupTable f 16 4)
                 (args   : Vector (ZKExpr f) 4)        : ZKOp f (ZKExpr f)
| MuxLookup      (chunks : Vector (ZKExpr f) 4)
                 (cases  : Array (ZKExpr f × ComposedLookupTable f 16 4))
                                                     : ZKOp f (ZKExpr f)
| RamNew         (size   : Nat)                       : ZKOp f (RAM f)
| RamRead        (ram    : RAM f) (addr  : ZKExpr f)  : ZKOp f (ZKExpr f)
| RamWrite       (ram    : RAM f) (addr v: ZKExpr f)  : ZKOp f PUnit

/-- Type for the ZK circuit builder monad. -/
def ZKBuilder (f : Type) := FreeM (ZKOp f)

instance : Monad (ZKBuilder f) := by
 unfold ZKBuilder
 infer_instance

instance : LawfulMonad (ZKBuilder f) := by
  unfold ZKBuilder
  infer_instance

namespace ZKBuilder

-- We define helper functions for each of the primitive operations in the DSL, using `liftM` to lift them to the `ZKBuilder` monad.

/-- Get a fresh witness variable. -/
def witness : ZKBuilder f (ZKExpr f) :=
  FreeM.lift ZKOp.AllocWitness

/-- Constrain two expressions to be equal in circuit. -/
def constrainEq (x y : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainEq x y)

/--
Helper function to create a single row of a R1CS constraint (Az * Bz = Cz).
Here's an example to constrain `b` to be a boolean (0 or 1):
```
constrainR1CS (b) (1 - b) (0)
```
-/
def constrainR1CS (a b c : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainR1CS a b c)

/--
Perform a MLE lookup into the given table with the provided argument chunks.
-/
def lookup (tbl : ComposedLookupTable f 16 4)
           (args : Vector (ZKExpr f) 4) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.Lookup tbl args)

/--
Helper function to perform a mux over a set of lookup tables.
We use zkLean to compute the product of every flag with the result of the lookup.
This corresponds to the [`prove_primary_sumcheck`](https://github.com/a16z/jolt/blob/main/jolt-core/src/jolt/vm/instruction_lookups.rs#L980) function in Jolt.
All flags in `flags_and_lookups` should be 0 or 1 with only a single flag being set to 1.
Example:
```
mux_lookup
    #v[arg0, arg1, arg2, arg3]
    #[
      (addFlag, addInstruction),
      (andFlag, andInstruction),
      ...
    ]
```
-/
def muxLookup (chunks : Vector (ZKExpr f) 4)
              (cases  : Array (ZKExpr f × ComposedLookupTable f 16 4))
  : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.MuxLookup chunks cases)

/--
Create a new oblivious RAM in circuit of the given size.
-/
def ramNew   (n : Nat)                   : ZKBuilder f (RAM f)       :=
  FreeM.lift (ZKOp.RamNew n)

/--
Perform an oblivious RAM read.
Here's an example of how you might perform a CPU load instruction:
```
-- INSTR: load rs_13 rd_7
let addr <- ram_read  ram_reg  13
let v    <- ram_read  ram_mem  addr
            ram_write ram_reg  7    v
```
-/
def ramRead  (r : RAM f) (a : ZKExpr f)  : ZKBuilder f (ZKExpr f)   :=
  FreeM.lift (ZKOp.RamRead r a)

/--
Perform an oblivious RAM write.
Here's an example of how you might perform a CPU load instruction:
```
-- INSTR: load rs_13 rd_7
let addr <- ram_read  ram_reg  13
let v    <- ram_read  ram_mem  addr
            ram_write ram_reg  7    v
```
-/
def ramWrite (r : RAM f) (a v : ZKExpr f): ZKBuilder f PUnit        :=
  FreeM.lift (ZKOp.RamWrite r a v)

end ZKBuilder

open ZKBuilder

/-- Execute one `ZKOp` instruction and update the `ZKBuilderState`. -/
def ZKOpInterp [Zero f] {β} (op : ZKOp f β) (st : ZKBuilderState f) : (β × ZKBuilderState f) :=
  match op with
  | ZKOp.AllocWitness =>
      let idx := st.allocated_witness_count
      (ZKExpr.WitnessVar idx, { st with allocated_witness_count := idx + 1 })
  | ZKOp.ConstrainEq x y =>
      ((), { st with constraints := (x, y) :: st.constraints })
  | ZKOp.ConstrainR1CS a b c =>
      ((), { st with constraints := (ZKExpr.Mul a b, c) :: st.constraints })
  | ZKOp.Lookup tbl args =>
      (ZKExpr.Lookup tbl args[0] args[1] args[2] args[3], st)
  | ZKOp.MuxLookup ch cases =>
      let sum := Array.foldl (fun acc (flag, tbl) =>
        acc + ZKExpr.Mul flag (ZKExpr.Lookup tbl ch[0] ch[1] ch[2] ch[3])) (ZKExpr.Literal (0 : f)) cases
      (sum, st)
  | ZKOp.RamNew n =>
      let id := st.ram_sizes.size
      ({ id := { ram_id := id } }, { st with ram_sizes := st.ram_sizes.push n })
  | ZKOp.RamRead ram a =>
      let i := st.ram_ops.size
      (ZKExpr.RamOp i, { st with ram_ops := st.ram_ops.push (RamOp.Read ram.id a) })
  | ZKOp.RamWrite ram a v =>
      ((), { st with ram_ops := st.ram_ops.push (RamOp.Write ram.id a v) })

/-- Convert a `ZKBuilder` computation into a `StateM` computation. -/
def toStateM [Zero f] {α : Type} (comp : ZKBuilder f α) : StateM (ZKBuilderState f) α :=
  comp.mapM ZKOpInterp

/--
Run a `ZKBuilder` program starting from an initial state.

The function walks through the program step-by-step:
• when it reaches `pure`, it simply returns the value without changing the state;
• when it sees an operation, it uses `ZKOpInterp` to update the state, then
  continues with the rest of the program.

Internally this is implemented with `FreeM.foldM`, which is quite literally a `fold` over the `FreeM` tree.
-/
def runFold [Zero f] (p : ZKBuilder f α) (st : ZKBuilderState f)
    : (α × ZKBuilderState f) :=
  (FreeM.foldM
    -- pure case : just return the value, leaving the state untouched
    (fun a => fun st => (a, st))
    -- bind case : interpret one primitive with `ZKOpInterp`, then feed the
    -- resulting value into the continuation on the updated state.
    (fun {_} op k => fun st =>
      let (b, st') := ZKOpInterp op st
      k b st')
    p) st

/--
A type is Witnessable if is has an associated building process.
-/
class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

/- Expressions of type `ZKExpr` are `Witnessable`. -/
instance: Witnessable f (ZKExpr f) where
  witness := witness

/- A vector of  `Witnessable` expressions is `Witnessable`. -/
instance [Witnessable f a]: Witnessable f (Vector a n) where
  witness :=
    let rec helper n : ZKBuilder f (Vector a n) :=
      match n with
      | 0 => pure (Vector.mkEmpty 0)
      | m+1 => do
        let w <- Witnessable.witness
        let v <- helper m
        pure (Vector.push v w)
    do
      helper n

open Std.Do
/-- `ZKBuilder` admits a weakest‐precondition interpretation in terms of the
`MPL` predicate–transformer semantics.  A builder computation manipulates an
implicit `ZKBuilderState`; therefore its predicate shape is `PostShape.arg
(ZKBuilderState f) .pure`.

The interpretation simply executes the computation with `runFold` and feeds the
result to the post-condition. -/

instance [Zero f] : WP (ZKBuilder f) (.arg (ZKBuilderState f) .pure) where
  wp {α} (x : ZKBuilder f α) :=
    -- We reuse the `StateT` instance for predicate transformers: run the
    -- builder starting from an initial state and hand the resulting
    -- `(value, state)` pair to the post-condition.
    PredTrans.pushArg (fun s =>
      PredTrans.pure (runFold x s))
