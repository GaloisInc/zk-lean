import Mathlib.Algebra.Field.Defs

inductive Subtable (f: Type) (n: Nat) where
  | SubtableMLE (mle : Vector f n -> f) : Subtable f n

def subtableFromMLE {n: Nat} (mle : Vector f n -> f) : Subtable f n := Subtable.SubtableMLE mle


-- `LookupTable` is the specification for table related part of `JoltInstruction` in the jolt codebase.
inductive ComposedLookupTable (f:Type) (n: Nat) (c: Nat) where
  | Table (m: Nat) (subtables: Vector (Subtable f n × Fin c) m) (combine_lookups: Vector f m -> f) : ComposedLookupTable f n c

def mkComposedLookupTable  {n:Nat} {m: Nat} {c: Nat} (subtables: Vector (Subtable f n × Fin c) m) (combine_lookups: Vector f m -> f) : ComposedLookupTable f n c:=
  ComposedLookupTable.Table m subtables combine_lookups


-- Evaluation function defining the semantics of `Subtable`.
def evalSubtable {f: Type} {n: Nat} (subtable: Subtable f n) (input: Vector f n): f :=
  match subtable with
  | Subtable.SubtableMLE mle => mle input



-- The function evaluates a `ComposedLookupTable` on an input.
-- The input is split in `c` chunks.
-- It applies the lookup subtables to the right chunks, and combine the lookups.
-- This corresponds to the Definition 2.6 of the Jolt paper
-- `T[r] = g(T_1[r_1], ... , T_k[r_1], T_{k+1}[r_2], ... , T_2k[r_2], ... T_{\alpha - (k + 1)}[r_c])`
-- With the difference that chunks do not necessarily come in order r_1, r_2, etc. but instead are enumerated via an index method from the argument `subtables`.
-- This definition corresponds also to Definition 2.1 of the "Verifying Jolt zkVM Lookup Semantics" article.
def evalComposedLookupTable {f: Type} {n: Nat} {c: Nat} (table: ComposedLookupTable f n c) (input: Vector (Vector f n) c) : f :=
  match table with
    | ComposedLookupTable.Table m1 subtables combine_lookups =>
      let l   := Vector.map (fun (t, i) => evalSubtable t input[i]) subtables
      combine_lookups l




-- - Option to define a function for the prover to do witness generation in a more efficient manner
-- 	- ex: Run xor instead of evaluating the MLE
--
-- - Indexed vs non-indexed lookups

-- inductive LookupTableTopLevel (f:Type) where
  -- Add: concatenate_lookups(vals, C, log2(M) as usize)
  -- And: concatenate_lookups(vals, C, log2(M) as usize / 2)
  -- mul: concatenate_lookups(vals, C, log2(M) as usize)
  -- mulu: concatenate_lookups(vals, C, log2(M) as usize)
  -- or: concatenate_lookups(vals, C, log2(M) as usize / 2)
  -- sll: concatenate_lookups(vals, C, (log2(M) / 2) as usize)
  -- sub: concatenate_lookups(vals, C, log2(M) as usize)
  -- xor: concatenate_lookups(vals, C, log2(M) as usize / 2)
  -- | ConcatenateLookups:
  -- beq: vals.iter().product::<F>()
  -- bge:  F::one() - SLTInstruction::<WORD_SIZE>(self.0, self.1).combine_lookups(vals, C, M)
  -- bgeu: // 1 - SLTU(x, y) =
  --      F::one() - SLTUInstruction::<WORD_SIZE>(self.0, self.1).combine_lookups(vals, C, M)
  -- bne: F::one() - vals.iter().product::<F>()
  -- div: virtual
  -- divu: virtual
  -- lb:
  -- lbu:
  -- lh:
  -- lhu:
  -- mulh: virtual
  -- mulhu: virtual
  -- rem: virtual
  -- remu: virtual
  -- sb: virtual
  -- sh: virtual
  -- slt: unique
  -- sltu: unique
  -- sra: vals.iter().sum()
  -- srl: vals.iter().sum()
  -- virtual_advice: todo
  -- virtual_assert_aligned_memory_access: todo
  -- virtual_assert_lte: todo
  -- virtual_assert_valid_div0: todo
  -- virtual_assert_valid_signed_remainder: todo
  -- virtual_assert_valid_unsigned: todo
  -- virtual_mode: todo
  -- virtual_movesign: todo
