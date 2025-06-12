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


inductive Free (f : Type -> Type) (a : Type) where
| pure : a -> Free f a
| bind : ∀ x, f x -> (x -> Free f a) -> Free f a

def Free.map {α β : Type} (F : Type → Type) (f : α → β) : Free F α → Free F β :=
λ FFa =>
match FFa with
| pure a => Free.pure (f a)
| bind X Fx k => Free.bind X Fx (λ z => map F f (k z))

instance : Functor (Free F) where
map := Free.map F

def bindFree {a b : Type} (F : Type → Type) (x : Free F a) (f : a → Free F b) : Free F b :=
match x with
| .pure a => f a
| .bind X Fx k => .bind X Fx (λ z => bindFree F (k z) f)

instance FreeMonad (F : Type → Type) : Monad (Free F) where
  pure := Free.pure
  bind := bindFree F

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
def ZKBuilder (f : Type) := Free (ZKOp f)

instance : Monad (ZKBuilder f) :=
  FreeMonad (ZKOp f)

/-- Provide a `Zero` instance for `ZKExpr`. -/
instance [Zero f] : Zero (ZKExpr f) where
  zero := ZKExpr.Literal 0

namespace ZKBuilder

def witness     : ZKBuilder f (ZKExpr f) :=
  .bind _ (ZKOp.AllocWitness) .pure

def constrainEq (x y : ZKExpr f) : ZKBuilder f PUnit :=
  .bind _ (ZKOp.ConstrainEq x y) .pure

def constrainR1CS (a b c : ZKExpr f) : ZKBuilder f PUnit :=
  .bind _ (ZKOp.ConstrainR1CS a b c) .pure

def lookup (tbl : ComposedLookupTable f 16 4)
           (v   : Vector (ZKExpr f) 4) : ZKBuilder f (ZKExpr f) :=
  .bind _ (ZKOp.Lookup tbl v) .pure

def muxLookup (chunks : Vector (ZKExpr f) 4)
              (cases  : Array (ZKExpr f × ComposedLookupTable f 16 4))
  : ZKBuilder f (ZKExpr f) :=
  .bind _ (ZKOp.MuxLookup chunks cases) .pure

def ramNew   (n : Nat)                   : ZKBuilder f (RAM f)       :=
  .bind _ (ZKOp.RamNew n) .pure
def ramRead  (r : RAM f) (a : ZKExpr f)  : ZKBuilder f (ZKExpr f)   :=
  .bind _ (ZKOp.RamRead r a) .pure
def ramWrite (r : RAM f) (a v : ZKExpr f): ZKBuilder f PUnit        :=
  .bind _ (ZKOp.RamWrite r a v) .pure

end ZKBuilder

open ZKBuilder

class Witnessable (f: Type) (t: Type) where
  /-- Witness a new `t` in circuit. -/
  witness : ZKBuilder f t

/-- Algebra that *executes* one primitive, updating the state. -/
def buildAlg [Zero f] {β} (op : ZKOp f β) (st : ZKBuilderState f) : (β × ZKBuilderState f) :=
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

/-- Run a `ZKBuilder` program, producing its result and the final state. -/
def build [Zero f] (p : ZKBuilder f α) (st : ZKBuilderState f)
    : (α × ZKBuilderState f) :=
  match p with
  | .pure a        => (a, st)
  | .bind _ op k   =>
      let (b, st') := buildAlg op st
      build (k b) st'

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
