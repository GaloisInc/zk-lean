import Mathlib.Algebra.Field.Defs
import Mathlib.Control.Fold
import ZkLean

def main : IO Unit :=
  IO.println s!"Hello!"




-- ZKProof 7 examples

def example1 [Field f] [Inhabited f] : ZKBuilder (ZKExpr f) := do
  let x: ZKExpr f <- witness
  let one: ZKExpr f := 1
  constrain (x * (x - one) === 0)
  return x

def eq8 [Field f] : Subtable f :=
  let product v := Traversable.foldl (. * .) 1 v.toList
  let mle a b := product (Vector.zipWith a b (λ x y => (x * x + (1 - x) * (1 - y))))
  SubtableFromMLE 8 mle

def eq32 [Field f] : LookupTable f :=
  mkLookupTable 4
    #[ (eq8, 0), (eq8, 1), (eq8, 2), (eq8, 3) ].toVector
    (fun results => results.foldl (· * ·) 1)

structure RISCVState (f: Type) where
  pc: ZKExpr f
  registers: Vector (ZKExpr f) 32
deriving instance Inhabited for RISCVState

def example2 [Field f] [Inhabited f] (prev_st : RISCVState f) : ZKBuilder (RISCVState f) := do
  let new_st: RISCVState f <- witness

  let r1 := prev_st.registers[1]
  let r2 := prev_st.registers[2]

  let isEq <- lookup eq32 r1 r2
  constrain (new_st.registers[0] === isEq)

  return new_st

-- structure RISCVState (backend: Type) where
--   pc: ZKRepr backend UInt32
--   registers: Vector (ZKRepr backend UInt32) 32

-- structure RISCVState (backend: Type) [c: ZKBackend backend] where
--   pc: ZKRepr backend
--   registers: Vector (ZKRepr backend) 32

-- inductive RISCVState backend [c: ZKBackend backend] where
-- -- | MkRISCVState : ZKRepr -> Vector ZKRepr 1 -> RISCVState backend
-- | MkRISCVState : ZKRepr -> List ZKRepr -> RISCVState backend
--
-- def test : RISCVState Jolt := RISCVState.MkRISCVState 1 [1]

-- structure RISCVState (backend : Type) where
--   pc: ZKRepr backend Unit
--   -- registers: List (zkrepr UInt32)

-- #check RISCVState.mk 32

-- structure [ZKRepr zkrepr] RISCVState (zkrepr : Type) where
--   pc: repr zkrepr UInt32
--   -- registers: List (zkrepr UInt32)

-- def example2 {zkrepr:Type} [ZKRepr1 zkrepr Unit Unit] : ZKBuilder (RISCVState (ZKRepr1 zkrepr Unit)) := do
-- def example2 {zkrepr:Type} : ZKBuilder (RISCVState zkrepr) := do
--   let new_st <- witness
--
--   pure new_st


-- #eval example1

-- #check -5
-- #check (Int.natAbs) -5




-- Jolt examples


def eqSubtable [Field f] : Subtable f := SubtableFromMLE 1 (λ x y => (x[0] * x[1] + (1 - x[0]) * (1 - x[1])))

-- forall x y : F . 0 <= x < 2^n && 0 <= y < 2^n => eqSubtable (bits x) (bits y) == (toI32 x == toI32 y)
