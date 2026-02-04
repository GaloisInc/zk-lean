import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Sha3.Circuit
import ZKLeanExamples.Sha3.Circuit.Not
import ZKLeanExamples.Sha3.Spec

open Std Do

def not64.soundness (felt : ZKExpr f) :
  ⦃ λ _e => ⌜eqF felt bv⌝ ⦄
  not64 felt
  ⦃ ⇓? s1 _e => ⌜eqF s1 (~~~bv)⌝ ⦄
  := by

  sorry

