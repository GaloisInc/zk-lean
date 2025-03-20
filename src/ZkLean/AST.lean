import Mathlib.Algebra.Field.Defs
import ZkLean.LookupTable

def Ident := Nat
deriving instance BEq, Ord, Hashable for Ident

-- TODO: Is this needed?
instance : OfNat (Ident) n where
  ofNat := n

def WitnessId := Nat
deriving instance BEq, Ord, LT, Hashable for WitnessId

-- TODO: Is this needed?
instance : OfNat (WitnessId) n where
  ofNat := n

inductive ZKExpr (f: Type) where
  | Literal : (lit: f) -> ZKExpr f
  | WitnessVar : (id: WitnessId) -> ZKExpr f
  | Add : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Sub : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Neg : (rhs: ZKExpr f) -> ZKExpr f
  | Mul : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Eq :  (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f -- TODO: possibly change this to | Eq : {a: Type u} -> (lhs: ZKExpr a) -> (rhs: ZKExpr a) -> ZKExpr (ULift Bool)
  | Lookup: (table: ComposedLookupTable f 16 4) -> (arg1: ZKExpr f) -> (arg2: ZKExpr f) -> ZKExpr f -- TODO fix these 16,4
infix:50    " === " => ZKExpr.Eq

instance [Inhabited f]: Inhabited (ZKExpr f) where
  default := ZKExpr.Literal default

instance [OfNat f n] : OfNat (ZKExpr f) n where
  ofNat := ZKExpr.Literal (OfNat.ofNat n)

instance [HAdd f f f] : HAdd (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hAdd := ZKExpr.Add

instance [HAdd f f f] : HAdd Nat (ZKExpr f) (ZKExpr f) where
  hAdd := sorry

instance [HSub f f f] : HSub (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hSub := ZKExpr.Sub

instance [HMul f f f] : HMul (ZKExpr f) (ZKExpr f) (ZKExpr f) where
  hMul := ZKExpr.Mul

-- #check OfNat.ofNat
instance [HMul f f f] : HMul (ZKExpr f) Nat (ZKExpr f) where
  hMul a b := sorry -- ZKExpr.Mul a (ZKExpr.Literal b) -- (OfNat.ofNat b))

-- instance : Coe Nat (ZKExpr f) where
--   coe x := sorry

structure RamId where 
  ram_id: Nat

structure RAM (f: Type) where
  id: RamId

