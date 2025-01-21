
def Ident := Nat
deriving instance BEq, Hashable for Ident

-- TODO: Rename this ZKExpr
inductive ZKVar (f: Type) where
  | Literal (lit: f) : ZKVar f
  | Var (ident: Ident) : ZKVar f
  | Add (lhs: ZKVar f) (rhs: ZKVar f) : ZKVar f
  | Mul (lhs: ZKVar f) (rhs: ZKVar f) : ZKVar f
deriving instance Inhabited for ZKVar

instance [OfNat f n] : OfNat (ZKVar f) n where
  ofNat := ZKVar.Literal (OfNat.ofNat n)

instance [HSub a a a] : HSub (ZKVar a) (ZKVar a) (ZKVar a) where
  hSub := ZKVar.Add

instance [HMul a a a] : HMul (ZKVar a) (ZKVar a) (ZKVar a) where
  hMul := ZKVar.Mul

