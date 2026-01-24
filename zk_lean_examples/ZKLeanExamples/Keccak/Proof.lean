
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

-- Soundness of keccakRound: the circuit correctly computes one round of Keccak-f
-- This composes the soundness of theta, rho_pi, chi, and iota
-- Proof: uses the soundness of each component to show the composition is sound
def keccakRound.soundness (s0 : State) (round : Fin 24) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  keccakRound s0 round
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.keccakRound s0_bv round)⌝ ⦄
  := by
  -- The proof relies on composing the soundness of theta, rho_pi, chi, and iota
  -- keccakRound s0 round = theta s0 >>= rho_pi >>= chi >>= (iota · round)
  -- SHA3.keccakRound s0_bv round = SHA3.iota (SHA3.chi (SHA3.rho_pi (SHA3.theta s0_bv))) round
  --
  -- When the component soundness proofs (theta.soundness, rho_pi.soundness,
  -- chi.soundness, iota.soundness) are complete, this proof can be completed
  -- by composing them using the bind rules for Hoare triples.
  sorry

-- Soundness of keccakF: the circuit correctly computes the full Keccak-f[1600] permutation
-- This is proved using Spec.foldlM_array with a loop invariant that tracks eqState

-- Loop invariant for the keccakF fold: after processing prefix rounds,
-- the circuit state equals the spec state from folding those rounds
def keccakF_invariant (s0_bv : SHA3.State) :
    Invariant (Array.finRange 24).toList State (.arg (ZKState f) (.except PUnit .pure)) :=
  ⟨fun ⟨cursor, acc⟩ => spred(⌜eqState acc (cursor.prefix.foldl (fun s i => SHA3.keccakRound s i) s0_bv)⌝),
   ExceptConds.true⟩

-- Step lemma: one round of keccakRound preserves the invariant
-- This uses keccakRound.soundness to show each iteration maintains eqState
theorem keccakF_step (s0_bv : SHA3.State)
    (pref : List (Fin 24)) (cur : Fin 24) (suff : List (Fin 24))
    (h : (Array.finRange 24).toList = pref ++ cur :: suff) (acc : State) :
    ⦃ (keccakF_invariant s0_bv).1 (⟨pref, cur :: suff, h.symm⟩, acc) ⦄
    keccakRound acc cur
    ⦃ (fun acc' => (keccakF_invariant s0_bv).1 (⟨pref ++ [cur], suff, by simp [h]⟩, acc'),
       (keccakF_invariant s0_bv).2) ⦄ := by
  simp only [keccakF_invariant, List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- Introduce the precondition: eqState acc (pref.foldl ... s0_bv)
  mintro h_pre ∀e
  -- Apply keccakRound.soundness with s0_bv instantiated to the folded prefix state
  let pref_state := pref.foldl (fun s i => SHA3.keccakRound s i) s0_bv
  mspec (keccakRound.soundness (s0_bv := pref_state) acc cur)

-- Lemma to convert between List.foldl and Array.foldl
-- Array.foldl f init arr = List.foldl f init arr.toList
theorem list_foldl_eq_array_foldl :
    List.foldl (fun s (i : Fin 24) => SHA3.keccakRound s i) s0_bv (Array.finRange 24).toList =
    Array.foldl (fun s i => SHA3.keccakRound s i) s0_bv (Array.finRange 24) := by
  rfl  -- By definition, Array.foldl is List.foldl on toList

def keccakF.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  keccakF s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.keccakF s0_bv)⌝ ⦄
  := by
  mintro h ∀e
  unfold keccakF SHA3.keccakF
  -- Apply the foldlM_array spec with our invariant and step proof
  -- The invariant tracks eqState through each round, and the step proof uses keccakRound.soundness
  mspec (Spec.foldlM_array (keccakF_invariant s0_bv) (keccakF_step s0_bv))

