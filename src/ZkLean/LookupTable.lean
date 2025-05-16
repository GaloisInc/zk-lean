import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Even

inductive Subtable (f: Type) (n: Nat) where
  | SubtableMLE (mle : Vector f n -> f) : Subtable f n

def subtableFromMLE {n: Nat} (mle : Vector f n -> f) : Subtable f n := Subtable.SubtableMLE mle


-- `LookupTable` is the specification for table related part of `JoltInstruction` in the jolt codebase.
inductive ComposedLookupTable
  (f:Type)
  (num_bits: Nat)
  (num_chunks: Nat) where
  | Table
    (num_subtables: Nat)
    (subtables: Vector (Subtable f num_bits × Fin num_chunks) num_subtables) (combine_lookups: Vector f num_subtables -> f):
    ComposedLookupTable f num_bits num_chunks


def mkComposedLookupTable  {num_bits:Nat} {num_subtables: Nat} {num_chunks: Nat} (subtables: Vector (Subtable f num_bits × Fin num_chunks) num_subtables) (combine_lookups: Vector f num_subtables -> f) : ComposedLookupTable f num_bits num_chunks:=
  ComposedLookupTable.Table num_subtables subtables combine_lookups


/--
  Evaluation function defining the semantics of `Subtable`.
--/
def evalSubtable {f: Type} {num_bits: Nat} (subtable: Subtable f num_bits) (input: Vector f num_bits): f :=
  match subtable with
  | Subtable.SubtableMLE mle => mle input


/--
  Evaluation function definite the semantics of `ComposedLookupTable`
  given an input that is partitioned into `c` chunks.

  It applies the indexed chunks to the corresponding subtables,
  and then it combines the lookups.

  This evaluation implements the Definition 2.6 of the Jolt paper
  `T[r] = g(T_1[r_1], ... , T_k[r_1], T_{k+1}[r_2], ... , T_2k[r_2], ... , T_{ α - (k + 1)}[r_c], ... , T_{α}[r_c])`
  With the difference that chunks do not come necessarily in order r_1, r_2, etc.
  but instead are determined by indices provided in `subtables`.
  It also aligns with Definition 2.1 of the "Verifying Jolt zkVM Lookup Semantics" article.
--/
def evalComposedLookupTable
  {f: Type}
  {num_bits: Nat}
  {num_chunks: Nat}
  (table: ComposedLookupTable f num_bits num_chunks)
  (input: Vector (Vector f num_bits) num_chunks) : f :=
  match table with
    | ComposedLookupTable.Table num_subtables subtables combine_lookups =>
      let l := Vector.map (fun (t, i) => evalSubtable t input[i]) subtables
      combine_lookups l


theorem add_even_halves (h : Even n) : (n / 2) + (n / 2) = n :=
by
  obtain ⟨k, Hk⟩ := h
  rw [←Nat.two_mul] at Hk
  rw [Hk]
  rw [Nat.mul_div_right]
  rw [Nat.two_mul]
  simp


-- def evalComposedLookupTableArgs
--   [Field f]
--   {num_bits: Nat}
--   {num_chunks: Nat}
--   (table: ComposedLookupTable f num_bits num_chunks)
--   (input: Vector f num_chunks) : f :=
--   let chunks := Vector.map (to_chunks · num_bits) input
--   evalComposedLookupTable table chunks
--   match table with
--     | ComposedLookupTable.Table num_subtables subtables combine_lookups =>
--       let chunks := Vector.map (to_chunks · num_bits) input
--       let bits1 := get_chunks arg1 (num_bits/2) num_chunks
--       let bits2 := get_chunks arg2 (num_bits/2) num_chunks
--       let comb
--         (a: Vector f (num_bits / 2))
--         (b: Vector f (num_bits / 2))
--         : Vector f (num_bits) :=
--         by
--           have ab : Vector f _ := Vector.append a b
--           rw [add_even_halves _] at ab
--           exact ab
--           exact h
--       let input : Vector (Vector f num_bits) num_chunks := Vector.zipWith comb bits1 bits2
--       evalComposedLookupTable table chunks
