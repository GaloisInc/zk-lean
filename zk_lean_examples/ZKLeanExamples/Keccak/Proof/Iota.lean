import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Spec

open Std Do

def iota.soundness (s0 : State) (round : Fin 24) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  iota s0 round
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.iota s0_bv round)⌝ ⦄
  := by

  sorry


