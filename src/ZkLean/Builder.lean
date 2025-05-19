import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable

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


-- TODO:
-- - Make this a free monad?
-- - Make this `def`
/-- Type for the ZK circuit builder monad. -/
abbrev ZKBuilder (f:Type) := StateM (ZKBuilderState f)

-- instance: Monad (ZKBuilder f) where
--   pure := StateT.pure
--   bind := StateT.bind

/-- Get a fresh witness variable. -/
def witnessf : ZKBuilder f (ZKExpr f) := do
  let old_state <- StateT.get
  let old_count := old_state.allocated_witness_count
  let new_count := old_count +1
  StateT.set { old_state with allocated_witness_count := new_count}
  pure (ZKExpr.WitnessVar old_count)

/--
A type is Witnessable if is has an associated building process.
-/
class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

/- Expressions of type `ZKExpr` are `Witnessable`. -/
instance: Witnessable f (ZKExpr f) where
  witness := witnessf

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


/-- Constrain two expressions to be equal in circuit. -/
def constrainEq (x: ZKExpr f) (y: ZKExpr f) : ZKBuilder f PUnit := do
  let old_state <- StateT.get
  StateT.set { old_state with constraints := (x, y) :: old_state.constraints }
  pure ()

/--
Helper function to create a single row of a R1CS constraint (Az * Bz = Cz).
Here's an example to constrain `b` to be a boolean (0 or 1):
```
constrainR1CS (b) (1 - b) (0)
```
-/
def constrainR1CS (a: ZKExpr f) (b: ZKExpr f) (c: ZKExpr f) : ZKBuilder f PUnit :=
  constrainEq (ZKExpr.Mul a b) c

/--
Perform a MLE lookup into the given table with the provided argument chunks.
-/
def lookup (table : ComposedLookupTable f 16 4) (chunks: Vector (ZKExpr f) 4): ZKBuilder f (ZKExpr f) :=
  let c0 := chunks[0]
  let c1 := chunks[1]
  let c2 := chunks[2]
  let c3 := chunks[3]
  pure (ZKExpr.Lookup table c0 c1 c2 c3)

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
def mux_lookup [Zero f]
  (chunk_queries: Vector (ZKExpr f) 4)
  (flags_and_lookups: (Array (ZKExpr f × ComposedLookupTable f 16 4)))
  : ZKBuilder f (ZKExpr f) := do
  let prods <- Array.mapM (λ (flag, table) => do
      let lookup_expr <- lookup table chunk_queries
      let r: ZKExpr f := flag * lookup_expr
      pure r
    ) flags_and_lookups
  pure (Array.sum prods)

/--
Create a new oblivious RAM in circuit of the given size.
-/
def ram_new (size : Nat) : ZKBuilder f (RAM f) := do
  let old_state <- StateT.get
  let ram_id := Array.size old_state.ram_sizes
  StateT.set { old_state with ram_sizes := Array.push old_state.ram_sizes size}
  pure { id := { ram_id := ram_id }}

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
def ram_read (ram : RAM f) (addr : ZKExpr f) : ZKBuilder f (ZKExpr f) := do
  let old_state <- StateT.get
  let ram_op := RamOp.Read ram.id addr
  let op_index := Array.size old_state.ram_ops
  StateT.set { old_state with ram_ops := Array.push old_state.ram_ops ram_op }
  pure (ZKExpr.RamOp op_index)

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
def ram_write (ram : RAM f) (addr : ZKExpr f) (value : ZKExpr f) : ZKBuilder f PUnit := do
  let old_state <- StateT.get
  let ram_op := RamOp.Write ram.id addr value
  StateT.set { old_state with ram_ops := Array.push old_state.ram_ops ram_op }
