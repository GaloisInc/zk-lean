import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.Not
import ZKLeanExamples.Keccak.Spec

open Std Do

def not64.soundness (felt : ZKExpr f) :
  ⦃ λ _e => ⌜eqF felt bv⌝ ⦄
  not64 felt
  ⦃ ⇓? s1 _e => ⌜eqF s1 (~~~bv)⌝ ⦄
  := by

  sorry

