

-- TODO: Debug this type family

class ZKBackend (backend: Type u) where
  ZKRepr : Type -> Type u

inductive Jolt where
| MkJolt : Jolt

instance : ZKBackend Jolt where
  -- ZKRepr : Type -> Type
  ZKRepr := fun
  | UInt32 => Nat
  -- | Unit => UInt32

#check ZKBackend.ZKRepr
#check @ZKBackend.ZKRepr

-- #check ZKBackend Unit
-- #check ZKBackend.ZKRepr Unit Unit
-- #eval (32: ZKBackend.ZKRepr Unit Unit)

-- def ZKRepr := Type -> Type -> Type
-- def ZKRepr : Type -> Type -> Type
-- abbrev ZKRepr : Type -> Type
-- | Unit => UInt32


-- class ZKRepr (a: Type) where
--   repr : Type -> Type
--   -- repr (t: Type) : Type

-- -- type F128p := Nat
--
-- class ZKRepr1 (s: Type) (t: Type) (u: Type) where
--
--
-- inductive Jolt where
-- instance : ZKRepr1 Jolt UInt32 (ZKExpr F128p) where

-- inductive Proxy (a : Type) where
-- | Proxy
--
-- class Foo (a : Type) where
--   MyTypeFamily : Proxy a -> Type
--
-- inductive Bar (c : Foo t)
-- | BarC (MyTypeFamily c) : Bar c



-- class Foo (a : Type u) where
--   MyTypeFamily : Type u
--
-- instance : Foo Nat where
--   MyTypeFamily := Bool
--
-- inductive Bar t [c: Foo t] where
-- | Bar : Foo.MyTypeFamily t -> Bar t
--
-- #check Bar
-- #check @Bar

-- def f : Bar Nat := Bar.Bar true
