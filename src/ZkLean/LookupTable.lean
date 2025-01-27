
import Mathlib.Algebra.Field.Defs

inductive LookupTable (f: Type) where
  | LookupTableMLE (n: Nat) (mle : Vector f n -> Vector f n -> f) : LookupTable f
  | ComposedLookupTable (n: Nat) (subtables: Vector (LookupTable f) n) (compose: Vector (LookupTable f) n -> F) : LookupTable f

def lookupTableFromMLE (n: Nat) (mle : Vector f n -> Vector f n -> f) : LookupTable f := LookupTable.LookupTableMLE n mle

def unaryLookupTableFromMLE (n: Nat) (mle : Vector f n -> f) : LookupTable f := LookupTable.LookupTableMLE n mle

-- - Option to define a function for the prover to do witness generation in a more efficient manner
-- 	- ex: Run xor instead of evaluating the MLE
-- 
-- - Indexed vs non-indexed lookups
