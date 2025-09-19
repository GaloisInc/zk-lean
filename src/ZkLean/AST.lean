import Mathlib.Algebra.Field.Defs
import ZkLean.LookupTable


/-- Type to identify witness variables -/
abbrev WitnessId := Nat
deriving instance BEq, Ord, LT, Hashable for WitnessId

/-- Type to identify a specific RAM -/
structure RamId where
  ram_id: Nat
deriving instance Inhabited for RamId

/-- Type for RAM -/
structure RAM (f: Type) where
  id: RamId
deriving instance Inhabited for RAM

/--
Type for expressions to define computation to be verified by a Zero-Knowledge protocol.

The expressions are parametrized by a field type `f`.
The construtors include the usual arithmetic operations.
It includes also a constructor for looking up values in a lookup table
and a constructor for RAM operations.
-/
inductive ZKExpr (f: Type) where
  | Literal : (lit: f) -> ZKExpr f
  | WitnessVar : (id: WitnessId) -> ZKExpr f
  | Add : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Sub : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Neg : (rhs: ZKExpr f) -> ZKExpr f
  | Mul : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | ComposedLookup: (table: ComposedLookupTable f 16 4) -> (c1: ZKExpr f) -> (c2: ZKExpr f) -> (c3: ZKExpr f) ->(c4: ZKExpr f) -> ZKExpr f -- TODO: this should be a Vector (ZKExpr f) 4 instead the 4 expressions
  | LookupMLE: (table: LookupTableMLE f 64) -> (e: ZKExpr f) -> ZKExpr f
  | RamOp : (op_index: Nat) -> ZKExpr f

instance [Inhabited f]: Inhabited (ZKExpr f) where
  default := ZKExpr.Literal default

instance [OfNat f n] : OfNat (ZKExpr f) n where
  ofNat := ZKExpr.Literal (OfNat.ofNat n)

instance [Zero f]: Zero (ZKExpr f) where
  zero := ZKExpr.Literal 0

instance: HAdd (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hAdd := ZKExpr.Add

instance: Add (ZKExpr f) where
  add := ZKExpr.Add

instance: HSub (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hSub := ZKExpr.Sub

instance: Neg (ZKExpr f) where
  neg := ZKExpr.Neg

instance: HMul (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hMul := ZKExpr.Mul
