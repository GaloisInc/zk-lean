import Mathlib.Algebra.Field.Defs

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
  | Mul : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Eq :  (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  -- | Lookup: LookupTable -> arg1 -> arg2 -> ZKExpr f
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

def t := ZKExpr.Mul (ZKExpr.Eq (ZKExpr.Literal 1) (ZKExpr.Literal 2))  (ZKExpr.Eq (ZKExpr.Literal 3) (ZKExpr.Literal 4))

#check t

def t1 := ZKExpr.Mul (1 === (2: ZKExpr Nat)) (3 === (4 : ZKExpr Nat))
