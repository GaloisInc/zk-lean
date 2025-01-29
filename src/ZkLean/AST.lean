
def Ident := Nat
deriving instance BEq, Hashable for Ident

inductive ZKExpr (f: Type) where
  | Literal (lit: f) : ZKExpr f
  | Var (ident: Ident) : ZKExpr f
  | Add (lhs: ZKExpr f) (rhs: ZKExpr f) : ZKExpr f
  | Mul (lhs: ZKExpr f) (rhs: ZKExpr f) : ZKExpr f
  | Eq  (lhs: ZKExpr f) (rhs: ZKExpr f) : ZKExpr f
deriving instance Inhabited for ZKExpr

instance [OfNat f n] : OfNat (ZKExpr f) n where
  ofNat := ZKExpr.Literal (OfNat.ofNat n)

instance [HSub a a a] : HSub (ZKExpr a) (ZKExpr a) (ZKExpr a) where
  hSub := ZKExpr.Add

instance [HMul a a a] : HMul (ZKExpr a) (ZKExpr a) (ZKExpr a) where
  hMul := ZKExpr.Mul
