
import ZKLean
import ZKLean.Formalism
import ZKLeanExamples.Keccak.Circuit
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Proof.And
import ZKLeanExamples.Keccak.Proof.Chi
import ZKLeanExamples.Keccak.Proof.Iota
import ZKLeanExamples.Keccak.Proof.Not
import ZKLeanExamples.Keccak.Proof.RhoPi
import ZKLeanExamples.Keccak.Proof.Shift
import ZKLeanExamples.Keccak.Proof.Theta
import ZKLeanExamples.Keccak.Proof.Xor
import ZKLeanExamples.Keccak.Spec

open Std Do

def keccakRound.soundness (s0 : State) (round : Fin 24) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  keccakRound s0 round
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.keccakRound s0_bv round)⌝ ⦄
  := by

  sorry

def keccakF.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  keccakF s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.keccakF s0_bv)⌝ ⦄
  := by

  sorry

