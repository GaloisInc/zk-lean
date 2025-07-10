import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import MPL
import MPL.Triple
import ZkLean
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Lean.Elab.Term
import Mathlib.Tactic.Ring
import Std.Tactic.BVDecide
import Mathlib.Tactic.Linarith


open Lean Meta Elab Term
open Std



def main : IO Unit :=
  IO.println s!"Hello!"




-- ZKProof 7 examples

def example1 [ZKField f] : ZKBuilder f (ZKExpr f) := do
  let x: ZKExpr f <- Witnessable.witness
  let one: ZKExpr f := 1
  constrainEq (x * (x - one)) 0
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

  let isEq <- lookup eq32 #v[r1, r1, r2, r2] -- Note: This example doesn't really make sense anymore.
  constrainEq new_st.registers[0] isEq

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

-- A[0] = C * 1 +  var[3] * 829 + ...
-- Example of what we extract from Jolt
-- TODO: Make a struct for the witness variables in a Jolt step. Automatically extract this from JoltInputs enum?
def uniform_jolt_constraint [ZKField f] (jolt_inputs: JoltR1CSInputs f) : ZKBuilder f PUnit := do
  constrainR1CS ((1 +  jolt_inputs.chunk_1 ) * 829) 1 1
  constrainR1CS 1 1 ((1 +  jolt_inputs.chunk_1 ) * 829)
  -- ...

--   ...
-- def non_uniform_jolt_constraint step_1 step_2 = do
--   constrainR1CS (step_1.jolt_flag * 123) (step_2.jolt_flag + 1) (1)
--   constrainR1CS (step_1.jolt_flag * 872187687 + ...) (step_2.jolt_flag + 1) (1)
--   ...

def run_circuit' [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Bool :=
  let (_circ_states, zk_builder) := StateT.run circuit default
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
def constrainEq2 [ZKField f] (a b : ZKExpr f) : ZKBuilder f PUnit := do
  -- NOTE: equivalently `constrainR1CS (a - b) 1 0`
  constrainR1CS a 1 b

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



def test [Field f] (x:f) : f := x

def one : ZMod 7 := 1
#eval test one

#eval run_circuit' circuit1 [one, 1]
#eval run_circuit' circuit1 [one, 2]


def circuit12 : ZKBuilder (ZMod 7) PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  constrainEq2 a b

#eval run_circuit' circuit12 [ (0: ZMod 7), (1: ZMod 7)]
#eval run_circuit' circuit12 [ (0: ZMod 7), (0: ZMod 7)]


#check instZKFieldZModOfNatNat_main
-- #check instWitness


theorem circuitEq2SoundTry [ZKField f]: (run_circuit' circuit1 [ (a: f), (a:f )] = true) := by
  unfold circuit1

  unfold run_circuit'
  unfold StateT.run
  -- unfold circuit1
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
  unfold StateT.instMonad -- instMonadZKBuilder
  unfold instWitnessableZKExpr
  simp
  unfold StateT.bind
  simp
  unfold witnessf
  simp_all
  -- unfold pure
  unfold constrainEq2
  unfold constrainR1CS
  unfold constrainEq
  unfold StateT.get
  unfold StateT.set
  simp
  -- unfold pure
  -- unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold StateT.instMonad -- instMonadZKBuilder
  simp
  unfold StateT.bind
  -- unfold StateT.pure
  simp
  unfold StateT.map
  simp

  -- now unfold constraints_semantics
  unfold semantics_constraints
  unfold semantics_zkexpr
  unfold semantics_zkexpr.eval
  unfold semantics_zkexpr.eval
  simp

  unfold semantics_constraints
  rfl


theorem circuitEq2Eval [ZKField f]: (run_circuit' circuit1 [ (a: f), (b: f)] = (a == b)) := by

  unfold run_circuit'
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
  unfold instWitnessableZKExpr
  simp
  unfold bind
  unfold Monad.toBind
  unfold StateT.instMonad -- instMonadZKBuilder
  simp
  unfold StateT.bind
  simp
  unfold witnessf
  simp
  -- unfold pure
  unfold constrainEq2
  unfold constrainR1CS
  unfold constrainEq
  unfold StateT.get
  unfold StateT.set
  simp
  -- unfold pure
  -- unfold Applicative.toPure
  unfold Monad.toApplicative
  unfold StateT.instMonad -- instMonadZKBuilder
  simp
  unfold StateT.bind
  unfold StateT.map
  simp

  unfold semantics_constraints
  unfold semantics_zkexpr
  unfold semantics_zkexpr.eval
  unfold semantics_zkexpr.eval
  simp
  unfold semantics_constraints
  simp


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
  ⦃λ s => s = old_s ⦄
  constrainEq2 a b
  ⦃⇓ _r s => s.constraints.length = old_s.constraints.length + 1⦄
  := by
  mintro h ∀old
  mpure h
  -- mwp
  simp [h]
  constructor

theorem constrainEq3Trivial [ZKField f] (a b c:ZKExpr f) :
  ⦃λ s => s = old_s ⦄
  constrainEq3 a b c
  ⦃⇓ _r s => s.constraints.length = old_s.constraints.length + 2⦄
  := by
  mintro h ∀old
  mpure h
  simp [h]
  unfold constrainEq3
  mspec (constrainEq2Trivial a b)
  mintro ∀s2
  mpure h
  rename' h => hAB
  mspec (constrainEq2Trivial b c)
  mintro ∀s3
  mpure h
  simp [h, hAB]

theorem constrainEq2Sound' [ZKField f] (a b:ZKExpr f) (witness: List f) :
  ⦃λ s => True ⦄ -- eval_circuit s witness ⦄
  constrainEq2 a b
  ⦃⇓ _r s =>
    ⌜ eval_circuit s witness ↔
    eval_exprf a s witness == eval_exprf b s witness ⌝
  ⦄
  := by

  sorry

set_option grind.warning false

theorem constrainEq3Transitive [ZKField f] (a b c:ZKExpr f) (witness: List f) :
  ⦃λ _s => True ⦄ -- s = s0⦄ -- eval_circuit s witness ⦄
  constrainEq3 a b c
  ⦃⇓ _r s =>
    ⌜ eval_circuit s witness →
    eval_exprf a s witness == eval_exprf c s witness ⌝
  ⦄
  := by
  mintro h0 ∀s0
  mpure h0
  unfold constrainEq3
  -- mwp

  mspec (constrainEq2Sound' a b witness)
  mcases h with hAB
  mintro ∀s1
  mpure hAB

  have hCompose :
    ⦃λ s => s = s1 ∧ True ∧ s = s1 ∧ s = s1⦄
    constrainEq2 b c
    ⦃⇓ _r s =>
      ⌜eval_circuit s witness → eval_circuit s1 witness⌝
      ∧
      ⌜ eval_circuit s witness ↔
      eval_exprf b s witness == eval_exprf c s witness ⌝
      ∧
      ⌜eval_exprf a s1 witness = eval_exprf a s witness⌝
      ∧
      ⌜eval_exprf b s1 witness = eval_exprf b s witness⌝
    ⦄
    := MPL.Triple.and (constrainEq2 b c)
       (previous_success (constrainEq2 b c) witness)
       (MPL.Triple.and (constrainEq2 b c)
         (constrainEq2Sound' b c witness)
         (MPL.Triple.and (constrainEq2 b c)
         (eval_const (constrainEq2 b c) witness a)
         (eval_const (constrainEq2 b c) witness b)))

  mspec hCompose

  mintro ∀s2
  simp
  intro hBC

  intro hS2'
  intro hA
  intro hB
  intro hS2

  have hEvalBC: eval_exprf b s2 witness = eval_exprf c s2 witness := by apply hS2'.mp hS2
  rw [← hEvalBC]

  have hCompose2: eval_circuit s2 witness → eval_circuit s1 witness := by
    exact hBC

  have hS1: eval_circuit s1 witness := by
    apply hCompose2 at hS2
    exact hS2

  have hP1: eval_exprf a s1 witness = eval_exprf b s1 witness := by
    simp at hAB
    grind
  have hP2: eval_exprf a s2 witness = eval_exprf b s2 witness := by
    rw [hA] at hP1
    rw [hB] at hP1
    exact hP1
  exact hP2

-- definitions from other files

def XOR_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*((1 - x[7])*x[15] + x[7]*(1 - x[15])) + 2*((1 - x[6])*x[14] + x[6]*(1 - x[14])) + 4*((1 - x[5])*x[13] + x[5]*(1 - x[13])) + 8*((1 - x[4])*x[12] + x[4]*(1 - x[12])) + 16*((1 - x[3])*x[11] + x[3]*(1 - x[11])) + 32*((1 - x[2])*x[10] + x[2]*(1 - x[10])) + 64*((1 - x[1])*x[9] + x[1]*(1 - x[9])) + 128*((1 - x[0])*x[8] + x[0]*(1 - x[8])))

def XOR_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (XOR_16, 0), (XOR_16, 1), (XOR_16, 2), (XOR_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*256*x[2] + 1*256*256*x[1] + 1*256*256*256*x[0])


def RTYPE_pure64_RISCV_XOR (rs2_val : BitVec 32) (rs1_val : BitVec 32) : BitVec 32 :=
  BitVec.xor rs2_val rs1_val

-- attempt at map_f_to_bv
-- def map_f_to_bv (rs1_val : ZMod 4139) : Option (BitVec 32) :=
--   let n := (rs1_val.val : Nat)
--   if n < 2^32 then
--     some (BitVec.ofNat 32 n)
--   else
--     none

def map_f_to_bv (rs1_val : ZMod 4139) : Option (BitVec 8) :=
  let n := (rs1_val.val : Nat)
  if n < 2^8 then
    some (BitVec.ofNat 8 n)
  else
    none

def bv_to_bool (bv : BitVec a) : Option Bool := if bv == 0 then some true else if bv == 1 then some false else none

-- def map_f_to_bv (rs1_val : ZMod 4139) : Option (BitVec 8) :=
--   let n := (rs1_val.val : Nat)
--   if n < 2^3 then
--     some (BitVec.ofNat 8 n)
--   else
--     none

def bool_to_bv (b: Bool) : (BitVec 8) := if b == true then  0 else 1
--if b == false then 1

instance : Fact (Nat.Prime 4139) := by sorry
instance : ZKField (ZMod 4139) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  chunk_to_bits {num_bits: Nat} f :=
    let bv : BitVec 13 := BitVec.ofFin (Fin.castSucc f)
    -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
        0
    ) (Vector.range num_bits)

instance : Witnessable (ZMod 4139) (ZMod 4139) := by sorry



set_option diagnostics true

def xor_circuit [ZKField f] : ZKBuilder f PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  let aa <- Witnessable.witness
  let bb <- Witnessable.witness
  let c <- Witnessable.witness
  let res <- lookup XOR_32_4_16 #v[a, aa, bb, b]
  constrainEq res c

#eval run_circuit xor_circuit default [0, one, one, one, 0]


abbrev ff := 4139
abbrev f := ZMod ff
abbrev b := Nat.log2 ff




def g (x y : f) : f := x + y

--structure RangeTuple where
  --lo : ℕ
  --hi : ℕ


lemma add_le_ff (x y : f) (a b : ℕ):
  ( x.val < a) ∧ (y.val < b) -> (x.val + y.val < a+ b)
  := by intro h1
        apply Nat.add_lt_add h1.left h1.right

lemma trans_range_ff (x y : f) (a b : ℕ):
(x.val + y.val < a + b) ∧ (x + y = z) /\ a+b < ff -> (z.val < a+ b) := by
  rintro ⟨h, h1, h2⟩
  subst h1
  rw [ZMod.val_add]
  rw [Nat.mod_eq_of_lt (h.trans h2)]
  exact h

lemma zmod_to_bitvec_add (x y : f):
    (x.val + y.val < ff) -> BitVec.ofNat b x.val + BitVec.ofNat b y.val = BitVec.ofNat b (x + y).val
    := by
      intro h
      rw [ZMod.val_add, Nat.mod_eq_of_lt h]
      exact (@BitVec.ofNat_add b x.val y.val).symm


lemma zmod_to_bitvec_mul (x y : f):
    (h : x.val * y.val < ff) ->
    BitVec.ofNat b x.val * BitVec.ofNat b y.val
      = BitVec.ofNat b (x * y).val := by
      intro h
      rw [@ZMod.val_mul ff x y, Nat.mod_eq_of_lt h]
      sorry

 -- active TODOs

 lemma BitVec.ofNat_mul {w a b : ℕ} :
  BitVec.ofNat w (a * b) =
    (BitVec.ofNat w a) * (BitVec.ofNat w b) := by
  -- BitVec multiplication is just modulo 2^w
  sorry


theorem ofNat_sub_ofNat_of_le (x y : Nat) (hy : y < 2 ^ w) (hlt : y ≤ x):
    BitVec.ofNat w x - BitVec.ofNat w y = BitVec.ofNat w (x - y) := by
    sorry


lemma sample_attempt (x y : f):
  --(1 - x) * y + x * (1-y) ∧
  (x.val < 2 ∧
  y.val < 2 ) ->
  ( map_f_to_bv ( (1 - x) * y + x * (1-y)) =
  some ( ( 1-  BitVec.ofNat 8 x.val) * (BitVec.ofNat 8 y.val) +  (BitVec.ofNat 8 x.val) * (1- BitVec.ofNat 8 y.val))) := by
  intros h
  rcases h with ⟨hx, hy⟩
  unfold map_f_to_bv
  dsimp
  simp
  rw [ZMod.val_add, ZMod.val_mul, ZMod.val_mul, ZMod.val_sub, ZMod.val_sub]
  simp
  --conv =>
    --rhs
    --arg 1
  rw [Nat.add_mod, Nat.mul_mod, Nat.mul_mod]
  rw [Nat.mod_eq_of_lt]
  simp
  rw [Nat.mul_mod]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  rw [ZMod.val_one]
  rw [BitVec.ofNat_add, BitVec.ofNat_mul,  BitVec.ofNat_mul, ofNat_sub_ofNat_of_le, ofNat_sub_ofNat_of_le]
  simp
  have ha : ZMod.val x ≤ 1 := Nat.le_of_lt_succ hx
  have hb : ZMod.val y ≤ 1 := Nat.le_of_lt_succ hy
  have hx := Nat.eq_zero_or_eq_succ_pred (ZMod.val x)
  have hy :=  Nat.eq_zero_or_eq_succ_pred (ZMod.val y)
  sorry
  exact Nat.lt_trans hy (by decide)
  exact Nat.le_of_lt_succ hy
  exact Nat.lt_trans hx (by decide)
  exact Nat.le_of_lt_succ hx
  sorry
  exact Nat.lt_trans hy (by decide)
  rw [ZMod.val_one]
  cases ZMod.val x with
    | zero => simp
    | succ x =>
        have : x ≤ 1 := Nat.le_of_lt_succ hx
  · simp -- x = 0 → succ x = 1 → 1 - 1 = 0 < 4139



  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry







  -- Since val x < 2, it must be 0 or 1
  have x_cases : ZMod.val x = 0 ∨ ZMod.val x = 1 := by Nat.eq_zero_or_eq_succ_pred (ZMod.val x)

  Nat.lt_succ_iff.mp hx |>.le_iff_eq_or_lt.symm ▸ Or.inr (by linarith)

  -- Similarly for y
  have y_cases : ZMod.val y = 0 ∨ ZMod.val y = 1 := Nat.lt_succ_iff.mp hy |>.le_iff_eq_or_lt.symm ▸ Or.inr (by linarith)

  -- Case analysis
  cases x_cases <;> cases y_cases <;> simp_all
  all_goals decide
  rw [ZMod.val_sub]

  let x' : Fin n := (ZMod.finEquiv n).symm x

  fin_cases x'
  fin_cases y'
  obtain ⟨hx, hy⟩ := h
  fin_cases ZMod.val x



  have ha : ZMod.val x ≤ 1 := Nat.le_of_lt_succ h.left
  have hb : ZMod.val y ≤ 1 := Nat.le_of_lt_succ h.right
  have hx := Nat.eq_zero_or_eq_succ_pred (ZMod.val x)
  have hy :=  Nat.eq_zero_or_eq_succ_pred (ZMod.val y)
  cases hx with
    | inl hx1 =>
      cases hy with
        | inl hy1 => rw [hx1, hy1]  norm_num
        | inr hy2
    | inr h2 =>




  cases hx hy with
  | inl hx0 =>
    -- x = 0
    have hxa : ZMod.val x = 0 := hx0
    -- Now do same for y
    have hy := Nat.eq_zero_or_eq_succ_pred (ZMod.val y)
    cases hy with
    | inl hy0 => exact ⟨Or.inl hxa, Or.inl hy0⟩
    | inr hy1 =>
      -- Then y = succ (pred y) ≤ 1 ⇒ pred y = 0 ⇒ y = 1
      have : Nat.pred (ZMod.val y) = 0 := by
        cases Nat.le_zero_iff.mp (Nat.le_of_succ_le hb)
        rfl
      rw [hy1, this]; exact ⟨Or.inl hxa, Or.inr rfl⟩
  | inr hx1 =>
    -- Then x = succ (pred x) ≤ 1 ⇒ pred x = 0 ⇒ x = 1
    have : Nat.pred (ZMod.val x) = 0 := by
      cases Nat.le_zero_iff.mp (Nat.le_of_succ_le ha)
      rfl
    rw [hx1, this]
    -- Now same for y
    have hy := Nat.eq_zero_or_eq_succ_pred (ZMod.val y)
    cases hy with
    | inl hy0 => exact ⟨Or.inr rfl, Or.inl hy0⟩
    | inr hy1 =>
      have : Nat.pred (ZMod.val y) = 0 := by
        cases Nat.le_zero_iff.mp (Nat.le_of_succ_le hb)
        rfl
      rw [hy1, this]; exact ⟨Or.inr rfl, Or.inr rfl⟩















  interval_cases ZMod.val x



  simp







-- lemma xor_to_bv (fv1 fv2 : Vector f 8) :
--   (fv1[0].val < 8 ∧ fv2[0].val <8 ∧
--   fv1[1].val < 8 ∧ fv2[1].val <8 ∧
--   fv1[2].val < 8 ∧ fv2[2].val <8 ∧
--   fv1[3].val < 8 ∧ fv2[3].val <8 ∧
--   fv1[4].val < 8 ∧ fv2[4].val <8 ∧
--   fv1[5].val < 8 ∧ fv2[5].val <8 ∧
--   fv1[6].val < 8 ∧ fv2[6].val <8 ∧
--   fv1[7].val < 8 ∧ fv2[7].val <8 )  ->
--    evalSubtable XOR_16 (Vector.append fv1 fv2) = evalSubtable XOR_16 (Vector.append fv1 fv2)  := by
--    intros H

-- (1 - fv1[7]) * fv2[7] + fv1[7] * (1 - fv2[7]) + 2 * ((1 - fv1[6]) * fv2[6] + fv1[6] * (1 - fv2[6])) +
--                 4 * ((1 - fv1[5]) * fv2[5] + fv1[5] * (1 - fv2[5])) +
--               8 * ((1 - fv1[4]) * fv2[4] + fv1[4] * (1 - fv2[4])) +
--             16 * ((1 - fv1[3]) * fv2[3] + fv1[3] * (1 - fv2[3])) +
--           32 * ((1 - fv1[2]) * fv2[2] + fv1[2] * (1 - fv2[2])) +
--         64 * ((1 - fv1[1]) * fv2[1] + fv1[1] * (1 - fv2[1])) +
--       128 * ((1 - fv1[0]) * fv2[0] + fv1[0] * (1 - fv2[0]))
lemma bool_to_bv_leads_to_binary (x : f) (bv : BitVec 8) (i : ℕ) (hi : i < 8) :
    some (bool_to_bv bv[i]) = map_f_to_bv x →
    x.val < 2 := by
    unfold map_f_to_bv
    dsimp
    split_ifs with leq
    intros H
    injection H with H
    unfold bool_to_bv at H
    split_ifs at H
    injection H with Hx
    injection Hx with Hx'
    rw [Nat.mod_eq_of_lt leq] at Hx'
    rw [Nat.mod_eq_of_lt] at Hx'
    exact (Hx'.symm ▸ Nat.zero_lt_succ 1)
    simp
    injection H with Hx
    injection Hx with Hx'
    rw [Nat.mod_eq_of_lt leq] at Hx'
    rw [Nat.mod_eq_of_lt] at Hx'
    rw [←Hx']
    simp
    norm_num
    simp




    dsimp Hx
    unfold BitVec.ofNat at H
    have h_fin := congrArg BitVec.toFin H
    simp only [BitVec.toFin, BitVec.zero] at h_fin
    unfold BitVec.toFin at h_fin


    rw [BitVec.ofNat_eq_zero] at H
    have hx : ZMod.val x = 0 := by
      rw [H]
      simp only [BitVec.ofNat_eq_zero]
    simp

lemma ZMod.eq_iff_val_bitvec  (a b : ZMod ff) :
  a = b ↔ BitVec.ofNat 8 a.val = BitVec.ofNat 8 b.val := by sorry

lemma ZMod.val_drop_mod (a : ZMod ff) (n:ℕ):
  (a.val < n) -> (n < ff) -> (a.val % ff = a.val) := by sorry


 lemma ZMod.move_1_sub_bit (a: ZMod ff):
  (a.val < 2)  -> (1-a).val= 1- a.val := by sorry

lemma ZMod_XOR (a b: ZMod ff) :
   (a.val < 2) -> (b.val < 2)  -> ((1 - a) * b + a * (1 - b)).val =  ((1 - a.val) * b.val + a.val * (1 - b.val)) := by sorry

lemma xor_sum_bound {x y : ℕ} (hx : x < 2) (hy : y < 2) :
  (1 - x) * y + x * (1 - y) ≤ 1 := by sorry

 lemma BitVec.ofNat_sub{w a b : ℕ} :
  BitVec.ofNat w (a - b) =
    (BitVec.ofNat w a) - (BitVec.ofNat w b) := by
  -- BitVec multiplication is just modulo 2^w
  sorry

 lemma bit_to_bv { a : ℕ} (w : ℕ) :
  a < 2 ↔ (BitVec.ofNat w a  = 0#w ∨ BitVec.ofNat w a = 1#w)
     := by
  sorry
set_option maxHeartbeats 2000000

lemma xor_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = map_f_to_bv foutput ->
   some (bool_to_bv bv1[7])  = map_f_to_bv fv1[0]  ->
   some (bool_to_bv bv1[6]) = map_f_to_bv fv1[1]  ->
   some (bool_to_bv bv1[5]) = map_f_to_bv fv1[2]  ->
   some (bool_to_bv bv1[4]) = map_f_to_bv fv1[3]  ->
   some (bool_to_bv bv1[3]) = map_f_to_bv fv1[4]  ->
  some (bool_to_bv bv1[2]) = map_f_to_bv fv1[5]  ->
   some (bool_to_bv bv1[1]) = map_f_to_bv fv1[6]  ->
   some (bool_to_bv bv1[0]) = map_f_to_bv fv1[7]  ->
  some (bool_to_bv bv2[7]) = map_f_to_bv fv2[0]  ->
  some (bool_to_bv bv2[6]) = map_f_to_bv fv2[1]  ->
  some (bool_to_bv bv2[5]) = map_f_to_bv fv2[2]  ->
  some (bool_to_bv bv2[4]) = map_f_to_bv fv2[3]  ->
  some (bool_to_bv bv2[3]) = map_f_to_bv fv2[4]  ->
  some (bool_to_bv bv2[2]) = map_f_to_bv fv2[5]  ->
  some (bool_to_bv bv2[1]) = map_f_to_bv fv2[6]  ->
  some (bool_to_bv bv2[0]) = map_f_to_bv fv2[7]  ->
  (bvoutput = BitVec.xor bv1 bv2)
  ->
  (foutput = evalSubtable XOR_16 (Vector.append fv1 fv2))
:= by
    intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    have h2_le: ZMod.val (fv1[0]) <2 := bool_to_bv_leads_to_binary fv1[0] bv1 7 (by decide : 7 < 8) h2
    have h3_le: ZMod.val (fv1[1]) <2 := bool_to_bv_leads_to_binary fv1[1] bv1 6 (by decide : 6 < 8) h3
    have h4_le: ZMod.val (fv1[2]) <2 := bool_to_bv_leads_to_binary fv1[2] bv1 5 (by decide : 5 < 8) h4
    have h5_le: ZMod.val (fv1[3]) <2 := bool_to_bv_leads_to_binary fv1[3] bv1 4 (by decide : 4 < 8) h5
    have h6_le: ZMod.val (fv1[4]) <2 := bool_to_bv_leads_to_binary fv1[4] bv1 3 (by decide : 3 < 8) h6
    have h7_le: ZMod.val (fv1[5]) <2 := bool_to_bv_leads_to_binary fv1[5] bv1 2 (by decide : 2 < 8) h7
    have h8_le: ZMod.val (fv1[6]) <2 := bool_to_bv_leads_to_binary fv1[6] bv1 1 (by decide : 1 < 8) h8
    have h9_le: ZMod.val (fv1[7]) <2 := bool_to_bv_leads_to_binary fv1[7] bv1 0 (by decide : 0 < 8) h9
    have h10_le: ZMod.val (fv2[0]) <2 := bool_to_bv_leads_to_binary fv2[0] bv2 7 (by decide : 7 < 8) h10
    have h11_le: ZMod.val (fv2[1]) <2 := bool_to_bv_leads_to_binary fv2[1] bv2 6 (by decide : 6 < 8) h11
    have h12_le: ZMod.val (fv2[2]) <2 := bool_to_bv_leads_to_binary fv2[2] bv2 5 (by decide : 5 < 8) h12
    have h13_le: ZMod.val (fv2[3]) <2 := bool_to_bv_leads_to_binary fv2[3] bv2 4 (by decide : 4 < 8) h13
    have h14_le: ZMod.val (fv2[4]) <2 := bool_to_bv_leads_to_binary fv2[4] bv2 3 (by decide : 3 < 8) h14
    have h15_le: ZMod.val (fv2[5]) <2 := bool_to_bv_leads_to_binary fv2[5] bv2 2 (by decide : 2 < 8) h15
    have h16_le: ZMod.val (fv2[6]) <2 := bool_to_bv_leads_to_binary fv2[6] bv2 1 (by decide : 1 < 8) h16
    have h17_le: ZMod.val (fv2[7]) <2 := bool_to_bv_leads_to_binary fv2[7] bv2 0 (by decide : 0 < 8) h17
    --rw [split_cases_ff] at h2_le h3_le h4_le h5_le h6_le h7_le h8_le h9_le h10_le h11_le h12_le h13_le  h14_le h15_le h16_le h17_le
    unfold map_f_to_bv at h1
    dsimp at h1
    split_ifs at h1 with h
    injection h1 with h1'
    rw [h1']
    rw [ZMod.eq_iff_val_bitvec]
    let r1 := (ZMod.val (evalSubtable XOR_16 (fv1.append fv2)))
    unfold XOR_16
    unfold evalSubtable
    simp
    unfold subtableFromMLE
    simp
    unfold Vector.append
    simp
    rw [ZMod.val_add]
    rw [ZMod.val_add]
    rw [ZMod.val_add]
    rw [ZMod.val_add]
    rw [ZMod.val_add]
    rw [ZMod.val_add]
    rw [ZMod.val_add]
    -- rw [BitVec.ofNat_add]
    rw [ZMod.val_mul]
    rw [ZMod.val_mul]
    rw [ZMod.val_mul]
    rw [ZMod.val_mul]
    rw [ZMod.val_mul]
    rw [ZMod.val_mul]
    rw [ZMod.val_mul]
    rw [ZMod_XOR fv1[7] fv2[7] h9_le h17_le]
    rw [ZMod_XOR fv1[6] fv2[6] h8_le h16_le]
    rw [ZMod_XOR fv1[5] fv2[5] h7_le h15_le]
    rw [ZMod_XOR fv1[4] fv2[4] h6_le h14_le]
    rw [ZMod_XOR fv1[3] fv2[3] h5_le h13_le]
    rw [ZMod_XOR fv1[2] fv2[2] h4_le h12_le]
    rw [ZMod_XOR fv1[1] fv2[1] h3_le h11_le]
    rw [ZMod_XOR fv1[0] fv2[0] h2_le h10_le]
    rw [ZMod.val_ofNat]
    rw [ZMod.val_ofNat]
    rw [ZMod.val_ofNat]
    rw [ZMod.val_ofNat]
    rw [ZMod.val_ofNat]
    rw [ZMod.val_ofNat]
    rw [ZMod.val_ofNat]
    simp
    have h0_ineq : (1 - ZMod.val fv1[0]) * ZMod.val fv2[0] + ZMod.val fv1[0] * (1 - ZMod.val fv2[0]) ≤ 1 := by apply xor_sum_bound h2_le h10_le
    have h1_ineq : (1 - ZMod.val fv1[1]) * ZMod.val fv2[1] + ZMod.val fv1[1] * (1 - ZMod.val fv2[1]) ≤ 1 := by apply xor_sum_bound h3_le h11_le
    have h2_ineq : (1 - ZMod.val fv1[2]) * ZMod.val fv2[2] + ZMod.val fv1[2] * (1 - ZMod.val fv2[2]) ≤ 1 := by apply xor_sum_bound h4_le h12_le
    have h3_ineq : (1 - ZMod.val fv1[3]) * ZMod.val fv2[3] + ZMod.val fv1[3] * (1 - ZMod.val fv2[3]) ≤ 1 := by apply xor_sum_bound h5_le h13_le
    have h4_ineq : (1 - ZMod.val fv1[4]) * ZMod.val fv2[4] + ZMod.val fv1[4] * (1 - ZMod.val fv2[4]) ≤ 1 := by apply xor_sum_bound h6_le h14_le
    have h5_ineq : (1 - ZMod.val fv1[5]) * ZMod.val fv2[5] + ZMod.val fv1[5] * (1 - ZMod.val fv2[5]) ≤ 1 := by apply xor_sum_bound h7_le h15_le
    have h6_ineq : (1 - ZMod.val fv1[6]) * ZMod.val fv2[6] + ZMod.val fv1[6] * (1 - ZMod.val fv2[6]) ≤ 1 := by apply xor_sum_bound h8_le h16_le
    have h7_ineq : (1 - ZMod.val fv1[7]) * ZMod.val fv2[7] + ZMod.val fv1[7] * (1 - ZMod.val fv2[7]) ≤ 1 := by apply xor_sum_bound h9_le h17_le
    have hlt :
    ((1 - ZMod.val fv1[7]) * ZMod.val fv2[7] + ZMod.val fv1[7] * (1 - ZMod.val fv2[7]) +
      2 * ((1 - ZMod.val fv1[6]) * ZMod.val fv2[6] + ZMod.val fv1[6] * (1 - ZMod.val fv2[6])) +
      4 * ((1 - ZMod.val fv1[5]) * ZMod.val fv2[5] + ZMod.val fv1[5] * (1 - ZMod.val fv2[5])) +
      8 * ((1 - ZMod.val fv1[4]) * ZMod.val fv2[4] + ZMod.val fv1[4] * (1 - ZMod.val fv2[4])) +
      16 * ((1 - ZMod.val fv1[3]) * ZMod.val fv2[3] + ZMod.val fv1[3] * (1 - ZMod.val fv2[3])) +
      32 * ((1 - ZMod.val fv1[2]) * ZMod.val fv2[2] + ZMod.val fv1[2] * (1 - ZMod.val fv2[2])) +
      64 * ((1 - ZMod.val fv1[1]) * ZMod.val fv2[1] + ZMod.val fv1[1] * (1 - ZMod.val fv2[1])) +
      128 * ((1 - ZMod.val fv1[0]) * ZMod.val fv2[0] + ZMod.val fv1[0] * (1 - ZMod.val fv2[0]))) <= 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 := by
         linarith [h0_ineq, h1_ineq, h2_ineq, h3_ineq, h4_ineq, h5_ineq, h6_ineq, h7_ineq]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hlt (by norm_num))]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_add]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_mul]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [BitVec.ofNat_sub]
    rw [bit_to_bv 8] at h2_le h3_le h4_le h5_le h6_le h7_le h8_le h9_le h10_le h11_le h12_le h13_le h14_le h15_le h16_le h17_le
    unfold map_f_to_bv at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    dsimp at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    split_ifs at h2 h3 h4 h5
    split_ifs at h6 h7 h8 h9
    split_ifs at h10 h11 h12 h13
    split_ifs at h14 h15 h16 h17
    simp at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    unfold bool_to_bv at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    let a := foutput.val
    have ha : foutput.val = a := rfl
    rw [ha]
    let b10:= ZMod.val fv1[0]
    have hb10 : ZMod.val fv1[0] = b10 := rfl
    rw [hb10] at h2_le h2
    rw [hb10]
    let b11 := ZMod.val fv1[1]
    have hb11 : ZMod.val fv1[1] = b11 := rfl
    rw [hb11] at h3_le h3
    rw [hb11]
    let b12 := ZMod.val fv1[2]
    have hb12 : ZMod.val fv1[2] = b12 := rfl
    rw [hb12] at h4_le h4
    rw [hb12]
    let b13 := ZMod.val fv1[3]
    have hb13 : ZMod.val fv1[3] = b13 := rfl
    rw [hb13] at h5_le h5
    rw [hb13]
    let b14 := ZMod.val fv1[4]
    have hb14 : ZMod.val fv1[4] = b14 := rfl
    rw [hb14] at h6_le h6
    rw [hb14]
    let b15 := ZMod.val fv1[5]
    have hb15 : ZMod.val fv1[5] = b15 := rfl
    rw [hb15] at h7_le h7
    rw [hb15]
    let b16 := ZMod.val fv1[6]
    have hb16 : ZMod.val fv1[6] = b16 := rfl
    rw [hb16] at h8_le h8
    rw [hb16]
    let b17 := ZMod.val fv1[7]
    have hb17 : ZMod.val fv1[7] = b17 := rfl
    rw [hb17] at h9_le h9
    rw [hb17]
    let b20:= ZMod.val fv2[0]
    have hb20 : ZMod.val fv2[0] = b20 := rfl
    rw [hb20] at h10_le h10
    rw [hb20]
    let b21 := ZMod.val fv2[1]
    have hb21 : ZMod.val fv2[1] = b21 := rfl
    rw [hb21] at h11_le h11
    rw [hb21]
    let b22 := ZMod.val fv2[2]
    have hb22 : ZMod.val fv2[2] = b22 := rfl
    rw [hb22] at h12_le h12
    rw [hb22]
    let b23 := ZMod.val fv2[3]
    have hb23 : ZMod.val fv2[3] = b23 := rfl
    rw [hb23] at h13_le h13
    rw [hb23]
    let b24 := ZMod.val fv2[4]
    have hb24 : ZMod.val fv2[4] = b24 := rfl
    rw [hb24] at h14_le h14
    rw [hb24]
    let b25 := ZMod.val fv2[5]
    have hb25 : ZMod.val fv2[5] = b25 := rfl
    rw [hb25] at h15_le h15
    rw [hb25]
    let b26 := ZMod.val fv2[6]
    have hb26 : ZMod.val fv2[6] = b26 := rfl
    rw [hb26] at h16_le h16
    rw [hb26]
    let b27 := ZMod.val fv2[7]
    have hb27 : ZMod.val fv2[7] = b27 := rfl
    rw [hb27] at h17_le h17
    rw [hb27]
    bv_normalize
    bv_decide


















--   -- at H
--       dsimp at H
--       simp at H



--       --rcases H with ⟨h1,h2⟩
--       rcases H with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,h12, h14, h15, h16, h18⟩
--       --unfold bool_to_bv at h2
--       unfold map_f_to_bv at h2
--       dsimp at h2
--       split_ifs at h2 with h2_le
--       simp at h2



--       injection h2
--       split_ifs at h2 with
--       split_ifs at h2 with h2_le
--       injection h2 with h2




--       ---injection h2 with h_eq

--       --unfold bool_to_bv at H
--       --unfold map_f_to_bv at H
--       --dsimp at H
--       --split_ifs at H
--       --split_ifs at h1 with h


--       --split_ifs at H



--       -- with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20

--       sorry
--       sorry





-- lemma xor_mle_one_chunk[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
--   some bvoutput = map_f_to_bv foutput ∧
--   some bv1[0] = bv_to_bool <$> map_f_to_bv fv1[0] ∧
--   some bv1[1] = bv_to_bool <$> map_f_to_bv fv1[1] ∧
--   some bv1[2] = bv_to_bool <$> map_f_to_bv fv1[2] ∧
--   some bv1[3] = bv_to_bool <$> map_f_to_bv fv1[3] ∧
--   some bv1[4] = bv_to_bool <$> map_f_to_bv fv1[4] ∧
--   some bv1[5] = bv_to_bool <$> map_f_to_bv fv1[5] ∧
--   some bv1[6] = bv_to_bool <$> map_f_to_bv fv1[6] ∧
--   some bv1[7] = bv_to_bool <$> map_f_to_bv fv1[7] ∧
--   some bv2[0] = bv_to_bool <$> map_f_to_bv fv2[0] ∧
--   some bv2[1] = bv_to_bool <$> map_f_to_bv fv2[1] ∧
--   some bv2[2] = bv_to_bool <$> map_f_to_bv fv2[2] ∧
--   some bv2[3] = bv_to_bool <$> map_f_to_bv fv2[3] ∧
--   some bv2[4] = bv_to_bool <$> map_f_to_bv fv2[4] ∧
--   some bv2[5] = bv_to_bool <$> map_f_to_bv fv2[5] ∧
--   some bv2[6] = bv_to_bool <$> map_f_to_bv fv2[6] ∧
--   some bv2[7] = bv_to_bool <$> map_f_to_bv fv2[7] ∧
--   bvoutput = BitVec.xor bv1 bv2
--   ↔
--   foutput = evalSubtable XOR_16 (Vector.append fv1 fv2)
-- := by sorry



-- lemma xor_mle[ZKField f]  (a b : ZMod 4139) :
--   map_f_to_bv a = some bv1 →
--   map_f_to_bv b = some bv2 →
--   RTYPE_pure64_RISCV_XOR bv1 bv2 = bv3 →
--   --bv3[0-8] := →
--   ⦃ λ _s => True ⦄
--     lookup XOR_32_4_16 #v[c1, c2, c3, c4]
--   ⦃⇓ _r s =>
--     ⌜ eval_circuit s [ ] ⌝
--   ⦄ := by


-- -- scratch work:
-- -- let b0 := Nat.mod (b.val : Nat)  256 →
--  --  let b1 = Nat.mod (b.val / 256) 256 →
--  --  some b2 = Nat.mod (b.val / 256^2) 256 →
--  --  some b3 =  Nat.mod (b.val / 256^3)  256 →
--  --  some a0 = Nat.mod a.val 256 →
--  -- some a1 = Nat.mod (a.val/ 256) 256 →
--  -- some a2 = Nat.mod (a.val / 256^2) 256 →
--   -- some a3 = Nat.mod (a.val / 256^3) 256 →
--   -- some x0 = a0 + 256 * b0 →
--   -- some x1 = a1 + 256 * b1 →
--  --  some x2 = a2 + 256 * b2 →
--  -- some x3 = a3 + 256 * b3 →
--  -- x[0] xor [x8]

-- -- MLE version of XOR
-- theorem xor_mle_equiv [ZKField f]  (a b : ZMod 4139) :
--   map_f_to_bv a = some bv1 →
--   map_f_to_bv b = some bv2 →
--   map_f_to_bv c = some bv3 →
--   RTYPE_pure64_RISCV_XOR bv1 bv2 = bv3 →
--   ⦃ λ _s => True ⦄
--     xor_circuit
--   ⦃⇓ _r s =>
--     ⌜ eval_circuit s [
--        ((Nat.mod a.val 256+ 256 * Nat.mod b.val 256 ): ZMod 4139),
--         ((Nat.mod (a.val/256) 256 + 256 * Nat.mod (b.val/256) 256):ZMod 4139),
--        ((Nat.mod (a.val/256^2) 256 + 256 * Nat.mod (b.val/256^2) 256): ZMod 4139),
--        ((Nat.mod (a.val/256^3) 256 + 256 * Nat.mod (b.val/256^3) 256): ZMod 4139),
--      c] ⌝
--   ⦄ := by
--   intros Hbv1 Hbv2 Hbv3 Hxor Hstate Htrue
--   unfold map_f_to_bv at Hbv1 Hbv2 Hbv3
--   dsimp at Hbv1
--   dsimp at Hbv2
--   dsimp at Hbv3
--   split_ifs at Hbv1 with h
--   split_ifs at Hbv2 with h1
--   split_ifs at Hbv3 with h2
--   injection Hbv1 with Hbv1
--   injection Hbv2 with Hbv2
--   injection Hbv3 with Hbv3
--   unfold RTYPE_pure64_RISCV_XOR at Hxor
--   unfold xor_circuit
--   simp only [XOR_32_4_16]
--   simp only [mkComposedLookupTable]
--   simp only [XOR_16]
--   simp only [lookup]
--   simp only [bind, pure]
--   simp only [eval_circuit]
--   simp only [constrainEq]
--   unfold StateT.bind StateT.pure StateT.get StateT.set
--   unfold semantics
--   simp only [ComposedLookupTable]
--   simp only [pure, subtableFromMLE, Subtable.SubtableMLE, ZKExpr.Lookup]
--   sorry


-- -- prove a lemma running XOR lookup table iff
-- -- XOR Is first chunk of bitvectors?
-- --- x1[0-8] XOR x1[8-16] = bv3[0-8]


--   unfold ZKExpr.eval ComposedLookupTable.eval Subtable.eval Subtable.evalFn Subtable.evalFnAt subtableFromMLE

--   unfold ZKExpr.Lookup at *



--    [ZKExpr.Lookup, ComposedLookupTable.Table, Subtable.SubtableMLE]
--   , Subtable.evalFn, Subtable.evalFnAt]

--    Vector.get, Vector.toList]
--   simp only [Finset.range, Finset.sum]




-- -- non MLE version of XOR_EQUIV
-- theorem XOR_EQUIV (rs2_val : ZMod 4139)  (rs1_val : ZMod 4139):
--     forall result resultf bv1 bv2, some bv1 = map_f_to_bv rs2_val
--     -> some bv2 = map_f_to_bv rs1_val
--     -> result = RTYPE_pure64_RISCV_XOR bv1 bv2
--     -> some result = map_f_to_bv resultf
--     -> run_circuit xor_circuit default [rs2_val, rs1_val, rs2_val, rs1_val, resultf] := by
--     intros result resultf bv1 bv2 Hbv1 Hbv2 Hres Hresf
--     -- simplify BV definitions
--     unfold map_f_to_bv at Hbv1 Hbv2 Hresf
--     dsimp at Hbv1
--     dsimp at Hbv2
--     dsimp at Hresf
--     split_ifs at Hbv1 with h
--     split_ifs at Hbv2 with h1
--     split_ifs at Hresf with h2
--     injection Hbv1 with Hbv1
--     injection Hbv2 with Hbv2
--     injection Hresf with Hresf
--     rw [Hres] at Hresf
--     unfold RTYPE_pure64_RISCV_XOR at Hresf
--     -- simplify Jolt definitions
--     unfold run_circuit xor_circuit
--     unfold lookup
--     unfold pure
--     unfold Applicative.toPure
--     unfold Monad.toApplicative
--     unfold StateT.instMonad
--     simp only [ZKExpr.Lookup]
--     unfold ZKExpr.Lookup
--     unfold XOR_32_4_16
--     simp only [XOR_32_4_16]
--     simp only [mkComposedLookupTable]
--     simp only [XOR_16]
--   simp only [lookup]
--   simp only [bind, pure]
--   simp only [eval_circuit]
--   simp only [constrainEq]





--     unfold Witnessable.witness
--     unfold instWitnessableZKExpr
--     simp
--     unfold StateT.run
--     unfold constrainEq
--     unfold StateT.get
--     unfold StateT.set
--     unfold bind
--     unfold Monad.toBind
--     unfold witnessf
--     unfold StateT.instMonad
--     unfold pure
--     unfold StateT.bind
--     unfold StateT.pure
--     unfold default
--     unfold








--     obtain ⟨a, s₁⟩ := StateT.run (Witnessable.witness : ZKBuilder (ZMod 4139) (ZMod 4139)) default
--     have h_constr₁ : constrainEq a rs2_val s₁ = pure () := by simp
-- have h_constr₂ : constrainEq b rs1_val s₂ = pure () := by simp
-- have h_constr₃ : constrainEq aa rs2_val s₃ = pure () := by simp
-- have h_constr₄ : constrainEq bb rs1_val s₄ = pure () := by simp
-- have h_constr₅ : constrainEq c resultf s₅ = pure () := by simp








--     set comp := do
--     let a ← Witnessable.witness
--     let b ← Witnessable.witness
--     let aa ← Witnessable.witness
--     let bb ← Witnessable.witness
--     let c ← Witnessable.witness
--     let res ← lookup XOR_32_4_16 #v[a, aa, bb, b]
--     constrainEq res c

--   -- Run the StateT monad on the default state
--   set result_state := StateT.run comp default
--     unfold StateT.run
--     cases



--     with state
--     cases


--     unfold Witnessable.witness
--     unfold instWitnessableZKExpr
--     unfold witnessf
--     unfold StateT.get
--     unfold StateT.set




--     simp Hresf

--   -- You now have the entire computation in terms of base definitions.
--   -- Try to compute or reduce further using simp or rfl
--     simp


--     -- under vs over constrained
--     -- under if circuit then BV to prove not go other direction
--     -- over if BV then circuit


-- --Question Circuits are not supposed to have any side effects so how do we
-- -- put lookup tables in the circuits or do we not do that?

-- -- MPL setting access to builder state
-- --- holds a ZK state (ZK builder)
