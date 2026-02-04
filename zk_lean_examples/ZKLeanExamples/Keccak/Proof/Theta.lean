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

-- Helper: getElem for cast-append-singleton pattern
@[simp]
theorem vector_cast_append_getElem_zero {α : Type} (a : α) (v : Vector α k) :
    (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(0 : Fin (k + 1))] = a := by
  have h1 : (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(0 : Fin (k + 1))] =
            (#v[a] ++ v)[(0 : Nat)] := Vector.getElem_cast (by omega)
  have h2 : (#v[a] ++ v)[(0 : Nat)] = #v[a][(0 : Nat)] := Vector.getElem_append_left (by omega)
  have h3 : #v[a][(0 : Nat)] = a := Vector.getElem_singleton (by omega)
  rw [h1, h2, h3]

@[simp]
theorem vector_cast_append_getElem_succ {α : Type} (a : α) (v : Vector α k) (i : Fin k) :
    (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(i.succ : Fin (k + 1))] = v[i] := by
  have h1 : (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(i.succ : Fin (k + 1))] =
            (#v[a] ++ v)[(i.val + 1 : Nat)] := Vector.getElem_cast (by omega)
  have h2 : (#v[a] ++ v)[(i.val + 1 : Nat)] = v[(i.val : Nat)] := by
    rw [Vector.getElem_append_right (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
  -- v[↑i] = v[i] by Fin.getElem_fin (which is rfl)
  rw [h1, h2, Fin.getElem_fin]

namespace Std.Do
@[spec]
theorem Spec.Vector_ofFnM {n : Nat} {α : Type}
  (inv : Prop)
  (f : Fin n → ZKBuilder f α)
  (postStep : Fin n → α → Prop)
  (hStep : ∀ (i : Fin n),
    ⦃ λ _e => ⌜inv⌝ ⦄
    f i
    ⦃ ⇓? s _e => ⌜postStep i s ∧ inv⌝ ⦄
  ) :
    ⦃ λ _e => ⌜inv⌝ ⦄
    Vector.ofFnM fun (x : Fin n) => f x
    ⦃ ⇓? v _e => ⌜inv ∧ ∀ (i : Fin n), postStep i v[i]⌝ ⦄
  := by
    induction n with
    | zero =>
      -- Base case: Vector.ofFnM f = pure #v[]
      simp only [Vector.ofFnM_zero]
      -- Use Triple.pure: need to show precond entails postcond applied to #v[]
      apply Triple.pure
      -- Goal: ⌜inv⌝ ⊢ₛ ⌜inv ∧ ∀ i : Fin 0, postStep i #v[][i]⌝
      apply SPred.pure_elim' (fun h_inv => ?_)
      apply SPred.pure_intro
      exact ⟨h_inv, fun i => i.elim0⟩
    | succ k ih =>
      -- Inductive case: use ofFnM_succ'
      rw [Vector.ofFnM_succ']
      mintro h_inv ∀e
      mpure h_inv
      -- First: run f 0
      mspec (hStep 0)
      mrename_i h0
      mpure h0
      -- Second: run recursive ofFnM
      have ih_inst := ih (f := fun i => f i.succ) (postStep := fun i => postStep i.succ)
        (fun i => hStep i.succ)
      mspec ih_inst
      mrename_i h_rest
      mpure h_rest
      -- Final: pure step to construct result
      mintro ∀e'
      mpure_intro
      obtain ⟨h_inv', h_all⟩ := h_rest
      obtain ⟨h_post0, _⟩ := h0
      constructor
      · exact h_inv'
      · intro i
        -- The result vector is ((#v[first_elem] ++ rest_vec).cast ...)
        -- For i=0, the element is first_elem which satisfies h_post0
        -- For i>0, the element is rest_vec[i-1] which satisfies h_all
        cases i using Fin.cases with
        | zero =>
          -- Use helper lemma for zero case
          simp only [vector_cast_append_getElem_zero]
          exact h_post0
        | succ i' =>
          -- Use helper lemma for succ case
          simp only [vector_cast_append_getElem_succ]
          exact h_all i'
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
set_option maxHeartbeats 400000
def theta.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  theta s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.theta s0_bv)⌝ ⦄
  := by
  mintro h_eq ∀e
  unfold theta SHA3.theta
  mpure h_eq

  let cInv := True
  let c := fun x => do xor64 (← xor64 (← xor64 (← xor64 (s0.get x 0) (s0.get x 1)) (s0.get x 2)) (s0.get x 3)) (s0.get x 4)
  let cBV : Fin 5 → BitVec 64 := fun x => s0_bv.get x 0 ^^^ s0_bv.get x 1 ^^^ s0_bv.get x 2 ^^^ s0_bv.get x 3 ^^^ s0_bv.get x 4
  let cPost : Fin 5 → ZKExpr f → Prop := (fun x e => eqF e (cBV x))
  let cBV := Vector.ofFn cBV
  have cStep: ∀ (i : Fin 5), ⦃ λ _e => ⌜cInv⌝ ⦄ c i ⦃ ⇓? s _e => ⌜cPost i s ∧ cInv⌝ ⦄ := by
    sorry
  mspec (Spec.Vector_ofFnM
    cInv
    c
    cPost
    cStep
  )
  rename_i cF
  mrename_i hC'
  mpure hC'

  let dInv := True
  let d := fun (x : Fin 5) => do xor64 (cF.get ⟨(x.val + 4) % 5, by omega⟩) (← rotateLeft64 (cF.get ⟨(x.val + 1) % 5, by omega⟩) 1)
  let dBV : Fin 5 → BitVec 64 := fun x => cBV[(x.val + 4) % 5]! ^^^ (cBV[(x.val + 1) % 5]!).rotateLeft 1
  let dPost : Fin 5 → ZKExpr f → Prop := fun x e => eqF e (dBV x)
  let dBV := Vector.ofFn dBV
  have dStep: ∀ (i : Fin 5), ⦃ λ _e => ⌜dInv⌝ ⦄ d i ⦃ ⇓? s _e => ⌜dPost i s ∧ dInv⌝ ⦄ := by
    sorry
  mspec (Spec.Vector_ofFnM
    dInv
    d
    dPost
    dStep
  )
  rename_i dF
  mrename_i hD'
  mpure hD'


  let laneInv := True
  let lane := fun (i : Fin 25) => do
    let x := i.val % 5
    let y := i.val / 5
    xor64 (s0.get ⟨x, by omega⟩ ⟨y, by omega⟩) dF[x]
  let laneBV := fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    s0_bv.get ⟨x, by omega⟩ ⟨y, by omega⟩ ^^^ dBV[x]
  let lanePost : Fin 25 → ZKExpr f → Prop := fun x e => eqF e (laneBV x)
  let laneBV := Vector.ofFn laneBV
  have laneStep: ∀ (i : Fin 25), ⦃ λ _e => ⌜laneInv⌝ ⦄ lane i ⦃ ⇓? s _e => ⌜lanePost i s ∧ laneInv⌝ ⦄ := by
    sorry
  mspec (Spec.Vector_ofFnM
    laneInv
    lane
    lanePost
    laneStep
  )
  rename_i laneF
  mrename_i hLane'
  mpure hLane'



  -- unfold eqState
  -- simp only [Vector.all_iff_forall]
  -- intro i _
  -- -- intro i hi
  -- simp [Vector.getElem_zip, eqF]

  -- interval_cases i --  <;> assumption
  -- · 
  --   simp [laneInv, lanePost] at hLane'
  --   apply (hLane' 0)




  -- -- Define the spec values we're comparing against
  -- let c_bv := specC s0_bv
  -- let d_bv := specD c_bv

  -- -- Step 1: Compute c vector
  -- -- The mspec tactic should apply Spec.Vector_ofFnM here
  -- -- For now, we use sorry since the Spec.Vector_ofFnM proof is incomplete
  -- sorry

