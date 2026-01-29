import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Proof.Iota
import ZKLeanExamples.Keccak.Proof.Shift
import ZKLeanExamples.Keccak.Proof.Xor
import ZKLeanExamples.Keccak.Spec

open Std Do

/-!
# Vector.ofFnM Hoare Triple Specification

This section provides a Hoare triple specification for `Vector.ofFnM` that allows
reasoning about monadic vector construction in a compositional way.

The key insight is that `Vector.ofFnM f` can be decomposed using `ofFnM_succ'`:
- First compute `f 0` to get the first element
- Then recursively compute the rest with indices shifted by 1
- Combine the results

We provide a spec that says: if for each index i, running `f i` in a state where
a precondition `P` holds produces a result satisfying `Q i`, and these operations
compose correctly, then `Vector.ofFnM f` produces a vector where each element
satisfies its corresponding property.
-/

namespace Std.Do

/--
Hoare triple specification for Vector.ofFnM.

Given:
- A monadic function `f : Fin n → m α` that builds each element
- An element property `elemProp : Fin n → α → Prop` that each element should satisfy
- A step proof showing that for each index i, running `f i` produces a result
  satisfying `elemProp i`

The spec concludes that `Vector.ofFnM f` produces a vector where each element
at index i satisfies `elemProp i`.
-/
@[spec]
theorem Spec.Vector_ofFnM {n : Nat} {α : Type u}
    [Monad m] [WPMonad m ps] [LawfulMonad m]
    {f : Fin n → m α}
    {elemProp : Fin n → α → Prop}
    {P : Assertion ps}
    {exceptConds : ExceptConds ps}
    (step : ∀ i : Fin n,
      Triple (f i) (spred(P)) (spred(fun a => ⌜elemProp i a⌝ ∧ P), exceptConds)) :
    Triple
      (Vector.ofFnM f)
      (spred(P))
      (spred(fun v => ⌜∀ i : Fin n, elemProp i v[i]⌝ ∧ P), exceptConds) := by
  -- The proof uses induction on n with ofFnM_succ' decomposition.
  -- Key steps:
  -- 1. Base case (n=0): Vector.ofFnM_zero gives pure #v[], trivially satisfies postcondition
  -- 2. Inductive case: Vector.ofFnM_succ' decomposes into f 0 >>= (ofFnM rest >>= pure)
  --    - Apply step 0 to get elemProp 0 for first element
  --    - Apply IH to get elemProp i.succ for remaining elements
  --    - Frame the pure fact (elemProp 0 a) through the recursive call
  --    - Combine in the final pure step using Vector cons indexing lemmas
  --
  -- The proof requires a frame lemma for pure facts through WP, which states:
  -- If P ⊢ₛ wp[x] (Q, R), then ⌜φ⌝ ∧ P ⊢ₛ wp[x] (⌜φ⌝ ∧ Q, R)
  -- This follows from the conjunctive property of wp.
  sorry

end Std.Do

/-!
# Theta Soundness Proof

The theta step of Keccak involves three Vector.ofFnM operations:
1. Compute column parity: c[x] = s[x,0] ⊕ s[x,1] ⊕ s[x,2] ⊕ s[x,3] ⊕ s[x,4]
2. Compute d values: d[x] = c[x-1] ⊕ rotl(c[x+1], 1)
3. Apply to state: s'[x,y] = s[x,y] ⊕ d[x]
-/

-- The c values computed from the spec
def specC (s_bv : SHA3.State) : Vector (BitVec 64) 5 :=
  Vector.ofFn fun x : Fin 5 =>
    s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2 ^^^ s_bv.get x 3 ^^^ s_bv.get x 4

-- The d values computed from the spec
def specD (c_bv : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 :=
  Vector.ofFn fun x : Fin 5 =>
    c_bv[(x.val + 4) % 5] ^^^ (c_bv[(x.val + 1) % 5]).rotateLeft 1

-- Helper: lane index from x, y coordinates
theorem lane_index_eq (x y : Fin 5) : (y.val * 5 + x.val) = x.val + y.val * 5 := by omega

-- Helper: converting between lane access styles
theorem state_get_lane_eq (s : State) (s_bv : SHA3.State) (x y : Fin 5)
    (h : eqState s s_bv) : eqF (s.get x y) s_bv.lanes[y.val * 5 + x.val] := by
  have := eqState_implies_lane_eq s s_bv ⟨y.val * 5 + x.val, by omega⟩ h
  unfold State.get
  simp at this ⊢
  exact this

-- Soundness for computing a single c[x] value (4 nested xors)
-- This theorem states the soundness of the inner loop body for computing c
theorem c_body_soundness (s : State) (s_bv : SHA3.State) (x : Fin 5) :
  ⦃ λ _e => ⌜eqState s s_bv⌝ ⦄
  (do xor64 (← xor64 (← xor64 (← xor64 (s.get x 0) (s.get x 1)) (s.get x 2)) (s.get x 3)) (s.get x 4))
  ⦃ ⇓? o _e => ⌜eqF o (s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2 ^^^ s_bv.get x 3 ^^^ s_bv.get x 4)⌝ ⦄ := by
  mintro h_eq ∀e
  mpure h_eq

  -- First xor: s.get x 0 ⊕ s.get x 1
  mspec (xor64.soundness (bv1 := s_bv.get x 0) (bv2 := s_bv.get x 1) _ _)
  · simp; exact ⟨state_get_lane_eq s s_bv x 0 h_eq, state_get_lane_eq s s_bv x 1 h_eq⟩
  mrename_i h1; mpure h1

  -- Second xor: (s.get x 0 ⊕ s.get x 1) ⊕ s.get x 2
  mspec (xor64.soundness (bv1 := s_bv.get x 0 ^^^ s_bv.get x 1) (bv2 := s_bv.get x 2) _ _)
  · simp; exact ⟨h1, state_get_lane_eq s s_bv x 2 h_eq⟩
  mrename_i h2; mpure h2

  -- Third xor
  mspec (xor64.soundness (bv1 := s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2) (bv2 := s_bv.get x 3) _ _)
  · simp; exact ⟨h2, state_get_lane_eq s s_bv x 3 h_eq⟩
  mrename_i h3; mpure h3

  -- Fourth xor (final operation - mspec completes the proof)
  mspec (xor64.soundness (bv1 := s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2 ^^^ s_bv.get x 3) (bv2 := s_bv.get x 4) _ _)
  simp; exact ⟨h3, state_get_lane_eq s s_bv x 4 h_eq⟩

-- Soundness for computing a single d[x] value
theorem d_body_soundness (c : Vector (ZKExpr f) 5) (c_bv : Vector (BitVec 64) 5) (x : Fin 5)
    (h_c : ∀ i : Fin 5, eqF (c.get i) (c_bv.get i)) :
  ⦃ λ _e => ⌜True⌝ ⦄
  (do xor64 (c.get ⟨(x.val + 4) % 5, by omega⟩) (← rotateLeft64 (c.get ⟨(x.val + 1) % 5, by omega⟩) 1))
  ⦃ ⇓? o _e => ⌜eqF o ((c_bv.get ⟨(x.val + 4) % 5, by omega⟩) ^^^ (c_bv.get ⟨(x.val + 1) % 5, by omega⟩).rotateLeft 1)⌝ ⦄ := by
  mintro _ ∀e

  -- rotateLeft64
  have hc1 : eqF (c.get ⟨(x.val + 1) % 5, by omega⟩) (c_bv.get ⟨(x.val + 1) % 5, by omega⟩) :=
    h_c ⟨(x.val + 1) % 5, by omega⟩
  have hc4 : eqF (c.get ⟨(x.val + 4) % 5, by omega⟩) (c_bv.get ⟨(x.val + 4) % 5, by omega⟩) :=
    h_c ⟨(x.val + 4) % 5, by omega⟩

  mspec (rotateLeft64.soundness (bv1 := c_bv.get ⟨(x.val + 1) % 5, by omega⟩) (bv2 := 1) _ _)
  · simp; exact ⟨hc1, rfl⟩
  mrename_i h_rot; mpure h_rot

  -- xor64 (final operation - mspec completes the proof)
  mspec (xor64.soundness (bv1 := c_bv.get ⟨(x.val + 4) % 5, by omega⟩) (bv2 := (c_bv.get ⟨(x.val + 1) % 5, by omega⟩).rotateLeft 1) _ _)
  simp; exact ⟨hc4, h_rot⟩

-- Soundness for computing a single lane[i] value in the final step
theorem lanes_body_soundness (s : State) (s_bv : SHA3.State)
    (d : Vector (ZKExpr f) 5) (d_bv : Vector (BitVec 64) 5)
    (i : Fin 25) (h_s : eqState s s_bv) (h_d : ∀ j : Fin 5, eqF (d.get j) (d_bv.get j)) :
  ⦃ λ _e => ⌜True⌝ ⦄
  (let x := i.val % 5
   let y := i.val / 5
   xor64 (s.get ⟨x, by omega⟩ ⟨y, by omega⟩) (d.get ⟨x, by omega⟩))
  ⦃ ⇓? o _e => ⌜eqF o (s_bv.lanes[i] ^^^ d_bv.get ⟨i.val % 5, by omega⟩)⌝ ⦄ := by
  mintro _ ∀e
  simp only []

  have hx_lt : i.val % 5 < 5 := Nat.mod_lt _ (by omega)
  have hy_lt : i.val / 5 < 5 := Nat.div_lt_of_lt_mul (by omega : i.val < 5 * 5)
  -- Prove index equality: (i.val / 5) * 5 + (i.val % 5) = i.val
  have idx_eq : i.val / 5 * 5 + i.val % 5 = i.val := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod i.val 5
  have hs_lane : eqF (s.get ⟨i.val % 5, hx_lt⟩ ⟨i.val / 5, hy_lt⟩) s_bv.lanes[i] := by
    have := state_get_lane_eq s s_bv ⟨i.val % 5, hx_lt⟩ ⟨i.val / 5, hy_lt⟩ h_s
    simp only [eqF] at this ⊢
    simp only [idx_eq] at this
    exact this
  have hd_elem : eqF (d.get ⟨i.val % 5, hx_lt⟩) (d_bv.get ⟨i.val % 5, hx_lt⟩) := h_d ⟨i.val % 5, hx_lt⟩

  -- xor64 (final operation - mspec completes the proof)
  mspec (xor64.soundness (bv1 := s_bv.lanes[i]) (bv2 := d_bv.get ⟨i.val % 5, hx_lt⟩) _ _)
  simp; exact ⟨hs_lane, hd_elem⟩

-- Helper: Show that specC gives the same values as SHA3.theta's c
theorem specC_eq_theta_c (s_bv : SHA3.State) (x : Fin 5) :
    (specC s_bv)[x] = s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2 ^^^ s_bv.get x 3 ^^^ s_bv.get x 4 := by
  simp [specC]

-- Helper: Show that specD gives the same values as SHA3.theta's d
theorem specD_eq_theta_d (c_bv : Vector (BitVec 64) 5) (x : Fin 5) :
    (specD c_bv)[x] = c_bv[(x.val + 4) % 5] ^^^ (c_bv[(x.val + 1) % 5]).rotateLeft 1 := by
  simp [specD]

-- Helper: Build eqState from element-wise eqF
theorem eqState_of_lanes_eq (lanes : Vector (ZKExpr f) 25) (lanes_bv : Vector (BitVec 64) 25)
    (h : ∀ i : Fin 25, eqF lanes[i] lanes_bv[i]) :
    eqState { lanes := lanes } { lanes := lanes_bv } := by
  unfold eqState
  simp only [Vector.all_iff_forall]
  intro i hi
  simp only [Vector.getElem_zip, eqF]
  exact h ⟨i, hi⟩

-- Main theta soundness theorem
-- Note: The theta circuit uses Vector.ofFnM which is a recursive combinator.
-- The proof requires integrating the Spec.Vector_ofFnM theorem with the mspec
-- tactic framework.
--
-- The proof structure is:
-- 1. Apply Spec.Vector_ofFnM for the c vector computation
-- 2. Apply Spec.Vector_ofFnM for the d vector computation
-- 3. Apply Spec.Vector_ofFnM for the lanes vector computation
-- 4. Combine the results to show eqState holds for the final state
--
-- The helper lemmas (c_body_soundness, d_body_soundness, lanes_body_soundness)
-- prove the soundness of individual element computations. The Spec.Vector_ofFnM
-- theorem (currently with sorry) lifts these to the full vector computations.
def theta.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  theta s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.theta s0_bv)⌝ ⦄
  := by
  mintro h_eq ∀e
  unfold theta SHA3.theta
  mpure h_eq

  -- Define the spec values we're comparing against
  let c_bv := specC s0_bv
  let d_bv := specD c_bv

  -- Step 1: Compute c vector
  -- The mspec tactic should apply Spec.Vector_ofFnM here
  -- For now, we use sorry since the Spec.Vector_ofFnM proof is incomplete
  sorry

