import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable
import ZkLean.FreeMonad

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

/-- Provide a `Zero` instance for `ZKExpr`. -/
instance [Zero f] : Zero (ZKExpr f) where
  zero := ZKExpr.Literal 0

namespace ZKBuilder

def witness : ZKBuilder f (ZKExpr f) :=
  FreeM.lift ZKOp.AllocWitness

def constrainEq (x y : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainEq x y)

def constrainR1CS (a b c : ZKExpr f) : ZKBuilder f PUnit :=
  FreeM.lift (ZKOp.ConstrainR1CS a b c)

def lookup (tbl : ComposedLookupTable f 16 4)
           (args : Vector (ZKExpr f) 4) : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.Lookup tbl args)

def muxLookup (chunks : Vector (ZKExpr f) 4)
              (cases  : Array (ZKExpr f × ComposedLookupTable f 16 4))
  : ZKBuilder f (ZKExpr f) :=
  FreeM.lift (ZKOp.MuxLookup chunks cases)

def ramNew   (n : Nat)                   : ZKBuilder f (RAM f)       :=
  FreeM.lift (ZKOp.RamNew n)

def ramRead  (r : RAM f) (a : ZKExpr f)  : ZKBuilder f (ZKExpr f)   :=
  FreeM.lift (ZKOp.RamRead r a)

def ramWrite (r : RAM f) (a v : ZKExpr f): ZKBuilder f PUnit        :=
  FreeM.lift (ZKOp.RamWrite r a v)

end ZKBuilder

open ZKBuilder

class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

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

Internally this is implemented with `FreeM.cataFreeM`, which is quite literally a `fold` over the `FreeM` tree.
-/
def runFold [Zero f] (p : ZKBuilder f α) (st : ZKBuilderState f)
    : (α × ZKBuilderState f) :=
  -- We first create a state-transformer by folding over the `FreeM` tree,
  -- then apply it to the supplied initial state.
  (FreeM.cataFreeM
    -- pure case : just return the value, leaving the state untouched
    (fun a => fun st => (a, st))
    -- bind case : interpret one primitive with `ZKOpInterp`, then feed the
    -- resulting value into the continuation on the updated state.
    (fun {_} op k => fun st =>
      let (b, st') := ZKOpInterp op st
      k b st')
    p) st

instance : Witnessable f (ZKExpr f) where
  witness := ZKBuilder.witness   -- smart constructor, pure DSL

instance [Witnessable f a] : Witnessable f (Vector a n) where
  witness :=
    let rec go : (m : Nat) → ZKBuilder f (Vector a m)
      | 0 => pure (Vector.mkEmpty 0)
      | Nat.succ m => do
          let w ← Witnessable.witness
          let v ← go m
          pure (Vector.push v w)
    go n
