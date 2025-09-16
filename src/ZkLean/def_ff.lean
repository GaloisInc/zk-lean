import ZkLean.Formalism
import Mathlib.Algebra.Field.ZMod
import ZkLean.valify

abbrev ff := 17179869203
abbrev f := ZMod ff
abbrev b := Nat.log2 ff



instance : Fact (Nat.Prime ff) := by sorry
instance : ZKField (ZMod ff) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  chunk_to_bits {num_bits: Nat} f :=
     let bv : BitVec 32 := BitVec.ofFin (Fin.castSucc 2^32)
  --   -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
         0
    ) (Vector.range num_bits)

instance : Witnessable (ZMod ff) (ZMod ff) := by sorry

open Mathlib.Tactic.Valify

instance NotTwo: GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry

#check (inferInstance : SubNegMonoid (ZMod ff))

instance IsThisTrue: SubNegMonoid (ZMod ff) :=
  inferInstance
