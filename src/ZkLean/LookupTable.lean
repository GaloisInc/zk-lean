import Mathlib.Algebra.Field.Defs

inductive Subtable (f: Type) where
  | SubtableMLE (n: Nat) (mle : Vector f n -> f) : Subtable f


def SubtableFromMLE {f: Type} (n: Nat) (mle : Vector f n -> f) : Subtable f := Subtable.SubtableMLE n mle

def unarySubtableFromMLE (n: Nat) (mle : Vector f n -> f) : Subtable f := Subtable.SubtableMLE n mle



-- `LookupTable` is the specification for table related part of `JoltInstruction` in the jolt codebase.
inductive LookupTable (f:Type) where
  | Table (n: Nat) (subtables: Vector (Subtable f × Nat) n) (combine_lookups: Vector f n -> f) : LookupTable f

def mkLookupTable  (n: Nat) (subtables: Vector (Subtable f × Nat) n) (combine_lookups: Vector f n -> f) : LookupTable f :=
  LookupTable.Table n subtables combine_lookups


-- In Jolt codebase `JoltInstruction::operand_chunks`
def operand_chunks [Field f] [Inhabited f] (_a: f) : (f × f) :=
  panic "TODO"


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
