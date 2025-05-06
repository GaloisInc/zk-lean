import Mathlib.Algebra.Field.Defs
import ZkLean.LookupTable


-- Type to identify witness variables
abbrev WitnessId := Nat
deriving instance BEq, Ord, LT, Hashable for WitnessId

-- Type to identify a specific RAM
structure RamId where
  ram_id: Nat
deriving instance Inhabited for RamId


structure RAM (f: Type) where
  id: RamId
deriving instance Inhabited for RAM

inductive ZKExpr (f: Type) where
  | Literal : (lit: f) -> ZKExpr f
  | WitnessVar : (id: WitnessId) -> ZKExpr f
  | Add : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Sub : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Neg : (rhs: ZKExpr f) -> ZKExpr f
  | Mul : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Eq :  (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f -- TODO: possibly change this to | Eq : {a: Type u} -> (lhs: ZKExpr a) -> (rhs: ZKExpr a) -> ZKExpr (ULift Bool)
  | Lookup: (table: ComposedLookupTable f 16 4) -> (c1: ZKExpr f) -> (c2: ZKExpr f) -> (c3: ZKExpr f) ->(c4: ZKExpr f) -> ZKExpr f -- TODO: this should be a Vector (ZKExpr f) 4 instead the 4 expressions

  --| MuxLookup:
  --  (chunk_queries: Array (ZKExpr f)) -> -- TODO: this should be a Vector (ZKExpr f) 4 instead of an Array
  --  (flags_and_lookups: (Array ((ZKExpr f) × ComposedLookupTable f 16 4))) ->
  --  ZKExpr f
  | RamOp : (op_index: Nat) -> ZKExpr f
infix:50    " === " => ZKExpr.Eq

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

