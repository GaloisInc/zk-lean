-- import Mathlib
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import ZkLean

def main : IO Unit :=
  IO.println s!"Hello!"




-- ZKProof 7 examples

def example1 [JoltField f] : ZKBuilder f (ZKExpr f) := do
  let x: ZKExpr f <- Witnessable.witness
  let one: ZKExpr f := 1
  constrain (x * (x - one) === 0)
  return x

def eq8 [Field f] : Subtable f 16 :=
  let product v := Traversable.foldl (. * .) 1 v.toList
  let first_half (v: Vector _ 16) : Vector _ 8 := Vector.take v 8
  let second_half (v: Vector _ 16) : Vector _ 8 := Vector.drop v 8
  let mle_on_pair a b:= product (Vector.zipWith (λ x y => (x * x + (1 - x) * (1 - y))) a b)
  let mle (v: Vector f 16): f := mle_on_pair (first_half v) (second_half v)
  subtableFromMLE mle

def eq32 [Field f] : ComposedLookupTable f 16 4 :=
  mkComposedLookupTable
    #[ (eq8, 0), (eq8, 1), (eq8, 2), (eq8, 3) ].toVector
    (fun results => results.foldl (· * ·) 1)

structure RISCVState (f: Type) where
  pc: ZKExpr f
  registers: Vector (ZKExpr f) 32
deriving instance Inhabited for RISCVState

instance: Witnessable f (RISCVState f) where
  witness := do
   let pc <- Witnessable.witness
   let registers <- Witnessable.witness
   pure { pc:=pc, registers := registers}


def step [JoltField f] (prev_st : RISCVState f) : ZKBuilder f (RISCVState f) := do
  let new_st: RISCVState f <- Witnessable.witness -- allocate a wire for witness

  let r1 := prev_st.registers[1]
  let r2 := prev_st.registers[2]

  let isEq <- lookup eq32 r1 r2
  constrain (new_st.registers[0] === isEq)

  return new_st


def rv_circ [JoltField f]: ZKBuilder f (List (RISCVState f))  := do
  let (init_state : RISCVState f) <- Witnessable.witness -- fix this
  let (state1 : RISCVState f) <- step init_state
  let (state2 : RISCVState f) <- step state1
  let (state3 : RISCVState f) <- step state2
  pure [init_state, state1, state2, state3]



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

def eqSubtable [JoltField f] : Subtable f 2 := subtableFromMLE (λ x => (x[0] * x[1] + (1 - x[0]) * (1 - x[1])))

-- forall x y : F . 0 <= x < 2^n && 0 <= y < 2^n => eqSubtable (bits x) (bits y) == (toI32 x == toI32 y)


structure JoltR1CSInputs (f : Type):  Type where
  chunk_1: ZKExpr f
  chunk_2: ZKExpr f
  /- ... -/

-- A[0] = C * 1 + var[3] * 829 + ...
-- Example of what we extract from Jolt
-- TODO: Make a struct for the witness variables in a Jolt step. Automatically extract this from JoltInputs enum?
def uniform_jolt_constraint [JoltField f] (jolt_inputs: JoltR1CSInputs f) : ZKBuilder f PUnit := do
  constrainR1CS ((1 +  jolt_inputs.chunk_1 ) * 829) 1 1
  constrainR1CS 1 1 ((1 +  jolt_inputs.chunk_1 ) * 829)
  -- ...

--   ...
-- def non_uniform_jolt_constraint step_1 step_2 = do
--   constrainR1CS (step_1.jolt_flag * 123) (step_2.jolt_flag + 1) (1)
--   constrainR1CS (step_1.jolt_flag * 872187687 + ...) (step_2.jolt_flag + 1) (1)
--   ...

def run_circuit [JoltField f] (circuit: ZKBuilder f a) (witness: List f) : Bool :=
  let (_circ_states, zk_builder) := StateT.run circuit default
  let b := constraints_semantics zk_builder.constraints witness
  b



def constrainEq2 [JoltField f] (a b : ZKExpr f) : ZKBuilder f PUnit := do
  -- constrainR1CS (a - b) 1 0
  constrainR1CS a 1 b

def circuit1 [JoltField f] : ZKBuilder f PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

def constrainEq3 [JoltField f] (a b c : ZKExpr f) : ZKBuilder f PUnit := do
  constrainEq2 a b
  constrainEq2 b c

def circuit2 [JoltField f] : ZKBuilder f PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  let c <- Witnessable.witness
  constrainEq3 a b c



instance : Fact (Nat.Prime 7) := by decide
instance : JoltField (ZMod 7) where

def test [Field f] (x:f) : f := x

def one : ZMod 7 := 1
#eval test one

#eval run_circuit circuit1 [one, 1]
#eval run_circuit circuit1 [one, 2]




-- instance : Fact (Nat.Prime 7) := by decide
-- instance : JoltField (ZMod 7) where


def circuit12 : ZKBuilder (ZMod 7) PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

#eval run_circuit circuit12 [ (0: ZMod 7), (1: ZMod 7)]
#eval run_circuit circuit12 [ (0: ZMod 7), (0: ZMod 7)]


-- instance : Fact (Nat.Prime 7) := by decide
-- instance instJoltFieldZMod7 : JoltField (ZMod 7) where

#check instJoltFieldZModOfNatNat_main
-- #check instWitness


theorem circuitEq2SoundTry [JoltField f]: (run_circuit circuit1 [ (a: f), (a:f )] = true) := by

  unfold run_circuit
  unfold StateT.run
  unfold circuit1
  unfold default
  unfold instInhabitedZKBuilderState
  unfold default
  simp
  unfold instInhabitedNat
  simp
  unfold instInhabitedList
  simp
  unfold Array.instInhabited
  simp
  unfold Witnessable.witness
  unfold bind
  unfold Monad.toBind
  unfold instMonadZKBuilder
  unfold instWitnessableZKExprOfJoltField
  simp
  unfold StateT.bind
  simp
  unfold witnessf
  simp
  unfold pure
  unfold constrainEq2
  unfold constrainR1CS
  unfold constrainEq
  unfold constrain
  unfold StateT.get
  unfold StateT.set
  simp
  unfold pure
  unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold instMonadZKBuilder
  simp
  unfold StateT.bind
  unfold StateT.pure
  simp

  -- now unfold constraints_semantics
  unfold constraints_semantics
  unfold semantics_zkexpr
  unfold semantics_zkexpr.eval
  unfold semantics_zkexpr.eval
  simp
  unfold semantics_zkexpr.eval
  simp
  unfold compare
  unfold instWitnessIdOrd
  unfold Nat.instOrd_mathlib
  unfold inferInstance
  unfold instOrdNat
  simp
  unfold compareOfLessAndEq
  simp

  -- constraints_semantics [] [a, a] = true
  unfold constraints_semantics
  simp


theorem circuitEq2Eval [JoltField f]: (run_circuit circuit1 [ (a: f), (b: f)] = (a == b)) := by

  unfold run_circuit
  unfold StateT.run
  unfold circuit1
  unfold default
  unfold instInhabitedZKBuilderState
  unfold default
  simp
  unfold instInhabitedNat
  simp
  unfold instInhabitedList
  simp
  unfold Array.instInhabited
  simp
  unfold Witnessable.witness
  unfold instWitnessableZKExprOfJoltField
  simp
  unfold bind
  unfold Monad.toBind
  unfold instMonadZKBuilder
  simp
  unfold StateT.bind
  simp
  unfold witnessf
  simp
  unfold pure
  unfold constrainEq2
  unfold constrainR1CS
  unfold constrainEq
  unfold constrain
  unfold StateT.get
  unfold StateT.set
  simp
  unfold pure
  unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold instMonadZKBuilder
  simp
  unfold StateT.bind
  unfold StateT.pure
  simp

  unfold constraints_semantics
  unfold semantics_zkexpr
  unfold semantics_zkexpr.eval
  unfold semantics_zkexpr.eval
  simp
  unfold semantics_zkexpr.eval
  simp
  unfold compare
  unfold instWitnessIdOrd
  unfold Nat.instOrd_mathlib
  unfold inferInstance
  unfold instOrdNat
  simp
  unfold compareOfLessAndEq
  simp

  intros h

  unfold constraints_semantics
  rfl

#check StateT.run_bind
attribute [local simp] StateT.run_bind

-- theorem1 : forall a b . a = b <=> run_circuit circuit1 [a, b]
theorem circuitEq2Sound [JoltField f] (x y : f) : (x = y ↔ run_circuit circuit1 [x, y]) := by
  -- -- grind

  apply Iff.intro
  intros acEq
  simp_all

  -- -- https://leanprover-community.github.io/mathlib4_docs/Init/Control/Lawful/Instances.html#StateT.run_bind
  -- apply (StateT.run_bind _ _ _)

  apply (circuitEq2SoundTry (a := y))

  intros h
  have h2 : _ := circuitEq2Eval (a := x) (b := y)
  rw [h] at h2
  simp_all


-- theorem2 : forall a b c . a = c <=> run_circuit circuit2 [a, b, c] by theorem1
theorem circuitEq3Transitive [JoltField f] (a b c : f) : (a = c ↔ run_circuit circuit2 [a, b, c]) := sorry
-- by
--   apply Iff.intro
--   intros acEq
--   sorry
