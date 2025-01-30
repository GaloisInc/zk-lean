
def Ident := Nat
deriving instance BEq, Hashable for Ident



inductive ZKType where
  | TyField: (f:Type) -> ZKType
  | TyBool: ZKType

inductive Expr (f: Type): ZKType -> Type where
  | Literal (lit: f) : Expr f (ZKType.TyField f)
  | Var (ident: Ident): Expr f (ZKType.TyField f)
  | Add (lhs: Expr f (ZKType.TyField f)) (rhs: Expr f (ZKType.TyField f)) : Expr f (ZKType.TyField f)
  | Mul (lhs: Expr f (ZKType.TyField f)) (rhs: Expr f (ZKType.TyField f)) : Expr f (ZKType.TyField f)
  | Eq (lhs: Expr f (ZKType.TyField f)) (rhs: Expr f (ZKType.TyField f)): Expr f ZKType.TyBool
--deriving instance Inhabited for Expr

instance [Inhabited f]: Inhabited (Expr f (ZKType.TyField f)) where
  default := Expr.Literal (default)

instance [Inhabited f]: Inhabited (Expr f (ZKType.TyBool)) where
  default := Expr.Eq default default

inductive ZKExpr (f: Type) where
  | Literal (lit: f) : ZKExpr f
  | Var (ident: Ident) : ZKExpr f
  | Add (lhs: ZKExpr f) (rhs: ZKExpr f) : ZKExpr f
  | Mul (lhs: ZKExpr f) (rhs: ZKExpr f) : ZKExpr f
  | Eq  (lhs: ZKExpr f) (rhs: ZKExpr f) : ZKExpr f
deriving instance Inhabited for ZKExpr

instance [OfNat f n] : OfNat (ZKExpr f) n where
  ofNat := ZKExpr.Literal (OfNat.ofNat n)

instance [HAdd a a a] : HAdd (ZKExpr a) (ZKExpr a) (ZKExpr a) where
  hAdd := ZKExpr.Add

instance [HSub a a a] : HSub (ZKExpr a) (ZKExpr a) (ZKExpr a) where
  hSub := ZKExpr.Add -- TODO: this should not be Add

instance [HMul a a a] : HMul (ZKExpr a) (ZKExpr a) (ZKExpr a) where
  hMul := ZKExpr.Mul
