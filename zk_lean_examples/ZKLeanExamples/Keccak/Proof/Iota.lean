import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Circuit.Iota
import ZKLeanExamples.Keccak.Proof.Xor
import ZKLeanExamples.Keccak.Spec

open Std Do

-- Helper: extract lane equality from eqState
theorem eqState_implies_lane_eq (s : State) (sBV : SHA3.State) (i : Nat) (hi : i < 25) :
    eqState s sBV = true → eqF s.lanes[i] sBV.lanes[i] := by
  intro h
  unfold eqState at h
  sorry

-- Helper: circuit roundConstants equals spec roundConstants
-- The circuit and spec round constants are the same values
theorem roundConstants_eqF (i : Nat) (hi : i < 24) :
    eqF (roundConstants[i]'hi) (SHA3.roundConstants[i]'hi) = true := by
  unfold eqF roundConstants SHA3.roundConstants
  -- The constants are identical so their eval and toNat should match
  sorry

-- Helper: eqState is preserved when updating the same lane with equal values
theorem eqState_set (s : State) (sBV : SHA3.State) (i : Nat) (hi : i < 25)
    (v : ZKExpr f) (vBV : BitVec 64)
    (h_state : eqState s sBV = true) (h_val : eqF v vBV = true) :
    eqState { lanes := s.lanes.set! i v } { lanes := sBV.lanes.set! i vBV } = true := by
  unfold eqState at *
  sorry

def iota.soundness (s0 : State) (round : Fin 24) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  iota s0 round
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.iota s0_bv round)⌝ ⦄
  := by
  mintro h_eq ∀e
  unfold iota SHA3.iota SHA3.State.set SHA3.State.get
  -- The circuit does: xor64 s0.lanes[0] roundConstants[round] >>= pure ∘ set
  -- The spec does: set lane 0 to (lane 0 ^^^ roundConstants[round])
  mspec (xor64.soundness (bv1 := s0_bv.lanes[0]) (bv2 := SHA3.roundConstants[round.val]) s0.lanes[0] roundConstants[round.val])
  -- Goal 1: Prove precondition for xor64.soundness
  · sorry
  -- Goal 2: Prove postcondition (eqState for updated state)
  · sorry


