
def Ident := Nat
deriving instance BEq, Hashable for Ident



inductive ZKType: Type (u+1) where
  | TyField: (f:Type u) -> ZKType
  | TyBool: ZKType

inductive ZKExpr: ZKType -> Type (u+1) where
  | Literal (f: Type u) (lit: f) : ZKExpr (ZKType.TyField f)
  | Var (ident: Ident): ZKExpr (ZKType.TyField f)
  | Add (lhs: ZKExpr (ZKType.TyField f)) (rhs: ZKExpr (ZKType.TyField f)) : ZKExpr (ZKType.TyField f)
  | Mul (lhs: ZKExpr (ZKType.TyField f)) (rhs: ZKExpr (ZKType.TyField f)) : ZKExpr (ZKType.TyField f)
  | Eq (lhs: ZKExpr (ZKType.TyField f)) (rhs: ZKExpr (ZKType.TyField f)): ZKExpr ZKType.TyBool
--deriving instance Inhabited for ZKExpr


instance [Inhabited f]: Inhabited (ZKExpr (ZKType.TyField f)) where
  default := ZKExpr.Literal f (default)


instance [OfNat f n] : OfNat (ZKExpr (ZKType.TyField f)) n where
  ofNat := ZKExpr.Literal f (OfNat.ofNat n)

instance [HAdd f f f] : HAdd (ZKExpr (ZKType.TyField f)) (ZKExpr (ZKType.TyField f)) (ZKExpr (ZKType.TyField f)) where
  hAdd := ZKExpr.Add

instance [HSub f f f] : HSub (ZKExpr (ZKType.TyField f)) (ZKExpr (ZKType.TyField f)) (ZKExpr (ZKType.TyField f)) where
  hSub := ZKExpr.Add -- TODO: this should not be Add

instance [HMul f f f] : HMul (ZKExpr (ZKType.TyField f)) (ZKExpr (ZKType.TyField f)) (ZKExpr (ZKType.TyField f)) where
  hMul := ZKExpr.Mul
