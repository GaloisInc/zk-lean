import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable

inductive RamOp (f : Type) where
  | Read  (ram_id: RamId) (addr: ZKExpr f)
  | Write (ram_id: RamId) (addr: ZKExpr f) (value: ZKExpr f)
deriving instance Inhabited for RamOp


structure ZKBuilderState (f : Type) where
  allocated_witness_count: Nat
  constraints: List (ZKExpr f)
  -- Array of sizes and array of operations for each RAM.
  ram_sizes: Array Nat
  ram_ops: (Array (RamOp f))
deriving instance Inhabited for ZKBuilderState


-- TODO: Make this a free monad?
abbrev ZKBuilder (f:Type) := StateM (ZKBuilderState f)
-- abbrev ZKBuilder (f:Type) := ReaderT (List f) StateM (ZKBuilderState f)

-- instance: Monad (ZKBuilder f) where
--   pure := StateT.pure
--   bind := StateT.bind

-- instance: HAndThen (ZKBuilder f) (ZKBuilder f) (ZKBuilder f) where
--   hAndThen := StateT.hAndThen

def witnessf : ZKBuilder f (ZKExpr f) := do
  let old_state <- StateT.get
  let old_count := old_state.allocated_witness_count
  let new_count := old_count +1
  StateT.set { old_state with allocated_witness_count := new_count}
  pure (ZKExpr.WitnessVar old_count)

-- A type is witnessable if it has an associated number of witnesses and
-- a function to recompose a type given a vector of values.
class Witnessable (f: Type) (t:Type) where
  witness : ZKBuilder f t

instance: Witnessable f (ZKExpr f) where
  witness := witnessf

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


def constrain (constraint: ZKExpr f) : ZKBuilder f PUnit := do
  let old_state <- StateT.get
  StateT.set { old_state with constraints := constraint :: old_state.constraints }
  pure ()

def constrainEq (x: ZKExpr f) (y: ZKExpr f) : ZKBuilder f PUnit :=
  constrain (ZKExpr.Eq x y)

def constrainR1CS (a: ZKExpr f) (b: ZKExpr f) (c: ZKExpr f) : ZKBuilder f PUnit :=
  constrainEq (ZKExpr.Mul a b) c

def lookup (table : ComposedLookupTable f 16 4) (a: ZKExpr f) (b: ZKExpr f): ZKBuilder f (ZKExpr f) :=
  pure (ZKExpr.Lookup table a b)

def ram_new (size : Nat) : ZKBuilder f (RAM f) := do
  let old_state <- StateT.get
  let ram_id := Array.size old_state.ram_sizes
  StateT.set { old_state with ram_sizes := Array.push old_state.ram_sizes size}
  pure { id := { ram_id := ram_id }}

-- INSTR: load rs_13 rd_42
-- addr <- ram_read  ram_reg  13     (implies there is a witness_rs)
-- v    <- ram_read  ram_mem  addr   (implies there is a witness_ram_addr)
--         ram_write ram_reg  42   v (implies there is a witness_rd)

def ram_read (ram : RAM f) (addr : ZKExpr f) : ZKBuilder f (ZKExpr f) := do
  let old_state <- StateT.get
  let ram_op := RamOp.Read ram.id addr
  let op_index := Array.size old_state.ram_ops
  StateT.set { old_state with ram_ops := Array.push old_state.ram_ops ram_op }
  pure (ZKExpr.RamOp op_index)

def ram_write (ram : RAM f) (addr : ZKExpr f) (value : ZKExpr f) : ZKBuilder f PUnit := do
  let old_state <- StateT.get
  let ram_op := RamOp.Write ram.id addr value
  StateT.set { old_state with ram_ops := Array.push old_state.ram_ops ram_op }
