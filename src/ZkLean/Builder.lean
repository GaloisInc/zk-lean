import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable

inductive RamOp (f : Type) where
  | Read (addr: ZKExpr f)
  | Write (addr: ZKExpr f) (value: ZKExpr f)

structure ZKBuilderState (f : Type) where
  -- environment: Std.HashMap Ident (ZKExpr f)
  allocated_witness_count: Nat
  constraints: List (ZKExpr f)
  -- Array of sizes and array of operations for each RAM.
  rams: Array (Nat × Array (RamOp f))
deriving instance Inhabited for ZKBuilderState

  -- TODO: environment? AST?

-- ZKRepr ??
-- ZKRepr Jolt u32 = F128p

-- TODO: Make this a free monad?
def ZKBuilder (f:Type) := StateM (ZKBuilderState f)

instance: Monad (ZKBuilder f) where
  pure := StateT.pure
  bind := StateT.bind

-- structure ZKBuilder (a: Type) where
--   runBuilder: ZKBuilderState -> (a, ZKBuilderState)

-- instance : Monad ZKBuilder where
--   pure _x :=
--     {
--       environment := Std.HashMap.empty,
--     } -- TODO
--   bind _opt _next :=
--     {
--       environment := Std.HashMap.empty,
--     } -- TODO

def witnessf : ZKBuilder f (ZKExpr f) := do
  /-let old_count <- StateT.modifyGet
    (fun old_state =>
      let (p :Nat) := old_state.allocated_wire_count
      (p, {old_state with allocated_wire_count := p + 1 })
    )
    -/
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
  let new_ram_id := Array.size old_state.rams
  StateT.set { old_state with rams := Array.push old_state.rams (size, #[]) }
  pure { id := { ram_id := new_ram_id }}

-- INSTR: load rs_13 rd_42
-- addr <- ram_read  ram_reg  13
-- v    <- ram_read  ram_mem  addr
--         ram_write ram_reg  42   v

def ram_read (ram : RAM f) (addr : ZKExpr f) : ZKBuilder f (ZKExpr f) := do
  let old_state <- StateT.get
  let ram_op := RamOp.Read addr
  let ram_id := ram.id.ram_id
  let (size, old_ram) := old_state.rams[ram_id]!
  let op_index := Array.size old_ram
  let updated_ram := Array.push old_ram ram_op
  let rams := Array.set! old_state.rams ram_id (size, updated_ram)
  StateT.set { old_state with rams := rams }
  pure (ZKExpr.RamOp ram.id op_index)

def ram_write (ram : RAM f) (addr : ZKExpr f) (value : ZKExpr f) : ZKBuilder f PUnit := do
  let old_state <- StateT.get
  let ram_op := RamOp.Write addr value
  let ram_id := ram.id.ram_id
  let (size, old_ram) := old_state.rams[ram_id]!
  let updated_ram := Array.push old_ram ram_op
  let rams := Array.set! old_state.rams ram_id (size, updated_ram)
  StateT.set { old_state with rams := rams }
