import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.Xor
import ZKLeanExamples.Keccak.Spec

open Std Do

def xor64.soundness (felt1 felt2 : ZKExpr f) :
  ⦃ λ _e => ⌜eqF felt1 bv1 && eqF felt2 bv2⌝ ⦄
  xor64 felt1 felt2
  ⦃ ⇓? o _e => ⌜eqF o (bv1 ^^^ bv2)⌝ ⦄
  := by

  sorry


