
def Ident := Nat
deriving instance BEq, Hashable for Ident



inductive ZKExpr : (Type 0) -> Type 1 where
  | Literal : {f: Type 0} -> (lit: f) -> ZKExpr f
  | Var : {f: Type 0} -> (ident: Ident) -> ZKExpr f
  | Add : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Sub : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Mul : (lhs: ZKExpr f) -> (rhs: ZKExpr f) -> ZKExpr f
  | Eq : {a: Type 0} -> (lhs: ZKExpr a) -> (rhs: ZKExpr a) -> ZKExpr Bool
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
