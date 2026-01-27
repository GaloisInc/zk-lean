import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Proof.Iota
import ZKLeanExamples.Keccak.Proof.Shift
import ZKLeanExamples.Keccak.Spec

open Std Do

def rho_pi.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  rho_pi s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.rho_pi s0_bv)⌝ ⦄
  := by
  mintro h ∀e
  unfold rho_pi
  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[0]) (bv2 := 0) _ _)
  rename_i h
  simp
  constructor
  · apply (eqState_implies_lane_eq _ _ 0 h)
  · decide

  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[6]) (bv2 := 44) _ _)
  rename_i h _
  simp
  intro heq
  constructor
  · apply (eqState_implies_lane_eq _ _ 6 h)
  · decide

  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[12]) (bv2 := 43) _ _)
  rename_i h _ _
  simp
  intro heq
  constructor
  · apply (eqState_implies_lane_eq _ _ 12 h)
  · decide

  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[18]) (bv2 := 21) _ _)
  rename_i h _ _ _
  simp
  intro heq
  constructor
  · apply (eqState_implies_lane_eq _ _ 18 h)
  · decide

  mspec (rotateLeft64.soundness (bv1 := s0_bv.lanes[24]) (bv2 := 14) _ _)
  rename_i h _ _ _ _
  simp
  intro heq
  constructor
  · apply (eqState_implies_lane_eq _ _ 24 h)
  · decide


  sorry


