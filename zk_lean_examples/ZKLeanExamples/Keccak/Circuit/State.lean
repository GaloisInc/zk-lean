
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs


-- From ArkLib: BN254 scalar
@[reducible]
def scalarFieldSize : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

abbrev f := ZMod scalarFieldSize

theorem ScalarField_is_prime : Nat.Prime scalarFieldSize := by
  -- Proof is in ArkLib
  sorry
instance : Fact (Nat.Prime scalarFieldSize) := ⟨ScalarField_is_prime⟩
instance : Field f := ZMod.instField scalarFieldSize

-- State of keccak
structure State where
  lanes : Vector f 25
