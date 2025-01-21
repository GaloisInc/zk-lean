
import Mathlib.Algebra.Field.Defs

inductive LookupTable (f: Type) where
  | LookupTableMLE (n: Nat) (mle : Vector f n -> Vector f n -> f) : LookupTable f

def lookupTableFromMLE (n: Nat) (mle : Vector f n -> Vector f n -> f) : LookupTable f := LookupTable.LookupTableMLE n mle

