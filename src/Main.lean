import Std.Do
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs

import ZkLean
import ZkLean.SimpSets

open Std.Do

def main : IO Unit :=
  IO.println s!"Hello!"

attribute [simp_Triple] Std.Do.Triple
attribute [simp_Triple] Std.Do.SPred.entails
attribute [simp_Triple] Std.Do.PredTrans.apply
attribute [simp_Triple] Std.Do.PredTrans.pure
attribute [simp_Triple] Std.Do.wp

-- ZKProof 7 examples

def example1 [ZKField f] : ZKBuilder f (ZKExpr f) := do
  let x: ZKExpr f <- Witnessable.witness
  let one: ZKExpr f := 1
  ZKBuilder.constrainEq (x * (x - one)) 0
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


def step [ZKField f] (prev_st : RISCVState f) : ZKBuilder f (RISCVState f) := do
  let new_st: RISCVState f <- Witnessable.witness -- allocate a wire for witness

  let r1 := prev_st.registers[1]
  let r2 := prev_st.registers[2]

  let isEq <- ZKBuilder.lookup eq32 #v[r1, r1, r2, r2] -- Note: This example doesn't really make sense anymore.
  ZKBuilder.constrainEq new_st.registers[0] isEq

  return new_st


def rv_circ [ZKField f]: ZKBuilder f (List (RISCVState f))  := do
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

def eqSubtable [ZKField f] : Subtable f 2 := subtableFromMLE (λ x => (x[0] * x[1] + (1 - x[0]) * (1 - x[1])))

-- forall x y : F . 0 <= x < 2^n && 0 <= y < 2^n => eqSubtable (bits x) (bits y) == (toI32 x == toI32 y)


structure JoltR1CSInputs (f : Type):  Type where
  chunk_1: ZKExpr f
  chunk_2: ZKExpr f
  /- ... -/

-- A[0] = C * 1 + var[3] * 829 + ...
-- Example of what we extract from Jolt
-- TODO: Make a struct for the witness variables in a Jolt step. Automatically extract this from JoltInputs enum?
def uniform_jolt_constraint [ZKField f] (jolt_inputs: JoltR1CSInputs f) : ZKBuilder f PUnit := do
  ZKBuilder.constrainR1CS ((1 +  jolt_inputs.chunk_1 ) * 829) 1 1
  ZKBuilder.constrainR1CS 1 1 ((1 +  jolt_inputs.chunk_1 ) * 829)
  -- ...

--   ...
-- def non_uniform_jolt_constraint step_1 step_2 = do
--   constrainR1CS (step_1.jolt_flag * 123) (step_2.jolt_flag + 1) (1)
--   constrainR1CS (step_1.jolt_flag * 872187687 + ...) (step_2.jolt_flag + 1) (1)
--   ...

attribute [simp_circuit] runFold

@[simp_circuit]
def run_circuit' [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Bool :=
  let (_circ_states, zk_builder) := runFold circuit default
  let b := semantics_constraints zk_builder.constraints witness (Array.empty)
  b



/-
def num_witnesses (circuit : ZKBuilder f a) : Nat :=
  let (_, state) := StateT.run circuit default
  state.allocated_witness_count

def shift_indices (constraints: List (ZKExpr f)) (i: Nat) : List (ZKExpr f) := panic "TODO"

def wellbehaved (circuit: ZKBuilder f a) : Prop :=
  -- all exprs only point to allocated witnesses
  -- only adds something to the constraints
  -- given the behaviors of the circuit with the default, you can also give the behavior of the circuit with another state
  forall s ,
    let (_circ_states, state1) := StateT.run circuit default
    let (_circ_states, state2) := StateT.run circuit s
    state2.allocated_witness_count = s.allocated_witness_count + state1.allocated_witness_count
    ∧ state2.constraints = s.constraints ++ shift_indices state1.constraints s.allocated_witness_count


theorem num_witnesses_seq (circuit1: ZKBuilder f a) (circuit2: ZKBuilder f b) :
     wellbehaved circuit1 ->
     wellbehaved circuit2 ->
     num_witnesses (do
       let _ <- circuit1
       circuit2
     ) = num_witnesses circuit1 + num_witnesses circuit2 := by
     sorry

theorem constraints_seq [ZKField f](c1: ZKBuilder f a) (c2: ZKBuilder f b) (witness1: List f) (witness2: List f) :
     wellbehaved c1 ->
     wellbehaved c2 ->
     witness1.length = num_witnesses c1 ->
     witness2.length = num_witnesses c2 ->
     run_circuit' (do
       let _ <- circuit1
       circuit2
     ) (witness1 ++ witness2) = run_circuit' circuit1 witness1 && run_circuit' circuit2 witness2 := by
  sorry

theorem num_witnesses_bind (circuit1: ZKBuilder f a) (circuit2: ZKBuilder f a) :
     wellbehaved circuit1 ->
     wellbehaved circuit2 ->
     num_witnesses (circuit1 >>= circuit2) = num_witnesses circuit1 + num_witnesses circuit2 := by
     sorry

theorem constraints_seq c1 c2 :
     wellbehaved circuit1 ->
     wellbehaved circuit2 ->
     witness1.length = num_witnesses c1
     witness2.length = num_witnesses c2
     run_constraints (circuit1 >> circuit2) (witness1 ++ witness2) = run_constraints circuit1 witness1 && run_constraints circuit2 witness2 := by
-/

-- {} constrainEq2 a b {a_f == b_f}
-- {} run_circuit (constrainEq2 a b) {state ws res => res <-> (eval a · ·  == eval b ws state)}
-- run_circuit : ReaderT [f] (ReaderT (ZKBuilderState f)) bool
@[simp_ZKBuilder]
def constrainEq2 [ZKField f] (a b : ZKExpr f) : ZKBuilder f PUnit := do
  -- NOTE: equivalently `constrainR1CS (a - b) 1 0`
  ZKBuilder.constrainR1CS a 1 b

@[simp_circuit]
def circuit1 [ZKField f] : ZKBuilder f PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

-- {} constrainEq3 a b c {a == c}
def constrainEq3 [ZKField f] (a b c : ZKExpr f) : ZKBuilder f PUnit := do
  constrainEq2 a b
  constrainEq2 b c

def circuit2 [ZKField f] : ZKBuilder f PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  let c <- Witnessable.witness
  constrainEq3 a b c

instance : Fact (Nat.Prime 7) := by decide
instance : ZKField (ZMod 7) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  chunk_to_bits {num_bits: Nat} f :=
    let bv : BitVec 3 := BitVec.ofFin (Fin.castSucc f)
    -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
        0
    ) (Vector.range num_bits)

#eval run_circuit' (f := ZMod 7) circuit1 [1, 1]
#eval run_circuit' (f := ZMod 7) circuit1 [1, 2]

def circuit12 : ZKBuilder (ZMod 7) PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

#eval run_circuit' circuit12 [0, 1]
#eval run_circuit' circuit12 [0, 0]

theorem circuitEq2SoundTry [ZKField f] (a : f) : (run_circuit' circuit1 [a, a] = true) := by
  simp [simp_circuit, simp_FreeM, simp_ZKBuilder, simp_ZKSemantics]

theorem circuitEq2Eval [ZKField f]: (run_circuit' circuit1 [ (a: f), (b: f)] = (a == b)) := by
  simp [simp_circuit, simp_FreeM, simp_ZKBuilder, simp_ZKSemantics]

#check StateT.run_bind
attribute [local simp] StateT.run_bind

-- theorem1 : forall a b . a = b <=> run_circuit circuit1 [a, b]
-- theorem1 : {TRUE} (circuit1 [a, b]) {a = b}
theorem circuitEq2Sound [ZKField f] (x y : f) : (x = y ↔ run_circuit' circuit1 [x, y]) := by
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

theorem constrainEq2Trivial [ZKField f] (a b:ZKExpr f) :
  ⦃λ s => ⌜s = old_s⌝⦄
  constrainEq2 a b
  ⦃⇓ _r s => ⌜s.constraints.length = old_s.constraints.length + 1⌝⦄
  := by
  mintro h ∀old
  mpure h
  -- mwp
  simp [h]
  constructor

theorem constrainEq3Trivial [ZKField f] (a b c:ZKExpr f) :
  ⦃λ s => ⌜s = old_s⌝⦄
  constrainEq3 a b c
  ⦃⇓ _r s => ⌜s.constraints.length = old_s.constraints.length + 2⌝⦄
  := by
  mintro h ∀old
  mpure h
  simp [h]
  unfold constrainEq3
  sorry
  -- mspec (constrainEq2Trivial a b)
  -- mintro ∀s2
  -- mpure h
  -- rename' h => hAB
  -- mspec (constrainEq2Trivial b c)
  -- mintro ∀s3
  -- mpure h
  -- simp [h, hAB]

  -- mintro h ∀old
  -- mpure h
  -- simp [h]
  -- unfold constrainEq3
  -- unfold constrainEq2
  -- unfold ZKBuilder.constrainR1CS
  -- simp
  -- unfold MPL.PredTrans.apply
  -- unfold bind
  -- unfold Monad.toBind
  -- unfold instMonadZKBuilder
  -- unfold inferInstance
  -- unfold FreeM.instMonad
  -- simp
  -- repeat unfold FreeM.bind
  -- constructor

@[simp]
lemma isSome_eq_true_iff {α : Type*} {o : Option α} :
  o.isSome = true ↔ ∃ x, o = some x :=
  by cases o <;> simp

theorem constrainEq2Sound' [ZKField f] (a b:ZKExpr f) (witness: List f) :
  ⦃λ s => ⌜True⌝⦄
  -- ⦃λ s => ⌜eval_circuit s witness⌝⦄
  constrainEq2 a b
  ⦃⇓ r s =>
    ⌜eval_circuit s witness ↔ eval_exprf a s witness = eval_exprf b s witness⌝⦄
  := by
  simp [simp_circuit, simp_FreeM, simp_Triple, simp_ZKBuilder, simp_ZKSemantics]
  intro s' -- Pre
  unfold ZKBuilderState.ram_sizes
  constructor
  · intro h
    cases h' : semantics_ram witness s'.3 s'.ram_ops
    · simp
    · case some v =>
      rw [h'] at h
      simp at *
      cases h₁ : semantics_zkexpr.eval witness v a
      · simp [h₁] at h
      · case some x =>
        simp [h₁] at h
        cases h₂ : semantics_zkexpr.eval witness v b
        · simp [h₂] at h
        · case some y =>
          simp [h₂] at h
          cases' h with xeqy constraints
          simp [xeqy]
  · intro h
    sorry
    -- cases h' : semantics_ram witness s'.3 s'.ram_ops
    -- · simp [h'] at Pre
    -- · case some v =>
    --   simp [h'] at h
    --   simp at *
    --   cases h₁ : semantics_zkexpr.eval witness v a
    --   · simp [h'] at Pre
    --     unfold semantics_constraints at Pre
    --     simp at Pre
    --     simp
    --     sorry
    --   · sorry

theorem constrainEq3Transitive [ZKField f] (a b c:ZKExpr f) (witness: List f) :
  -- ⦃λ s => ⌜eval_circuit s witness⌝ ⦄
  ⦃λ s => ⌜True⌝⦄
  constrainEq3 a b c
  ⦃⇓ r s =>
    ⌜eval_circuit s witness →
     eval_exprf a s witness = eval_exprf c s witness⌝⦄
  := by
  unfold constrainEq3
  mintro H1
  mintro ∀s1
  -- NOTE This gives a weird error:
  -- mspec constrainEq2Sound'
  -- NOTE Doing this instead fixes the next tactic:
  mspec (constrainEq2Sound' a b (witness := witness))
  mintro ∀s2
  sorry
