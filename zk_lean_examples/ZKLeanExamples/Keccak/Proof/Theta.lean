import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Spec

open Std Do

def theta.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  theta s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.theta s0_bv)⌝ ⦄
  := by

  sorry



