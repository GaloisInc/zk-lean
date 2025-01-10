
structure ZKVar (a: Type) where
  -- TODO: identifier

instance [OfNat a n] : OfNat (ZKVar a) n where
  ofNat := {}

instance [HSub a a a] : HSub (ZKVar a) (ZKVar a) (ZKVar a) where
  hSub _x _y := {}

instance [HMul a a a] : HMul (ZKVar a) (ZKVar a) (ZKVar a) where
  hMul _x _y := {}

-- TODO: Free monad?
structure ZKBuilder (a: Type) where
  -- TODO: environment? AST?

-- ZKRepr ??
-- ZKRepr Jolt u32 = F128p

instance : Monad ZKBuilder where
  pure _x := {} -- TODO
  bind _opt _next := {} -- TODO

-- def witness {t : Type} : ZKBuilder (ZKVar t) := 
def witness {t : Type} : ZKBuilder t := 
  {} -- TODO

def constrain (_constraint: ZKBuilder Bool) : ZKBuilder Unit := {}
def constrainEq (_x: ZKVar a) (_y: ZKVar a) : ZKBuilder Bool := {}
infix:50    " === " => constrainEq


structure LookupTable (f: Type) where

def lookup (_table : LookupTable f) (_:ZKVar f) (_:ZKVar f) : ZKBuilder (ZKVar f) := {}







-- TODO: Debug this type family

class ZKBackend (a: Type) where
  ZKRepr : Type -> Type

instance :ZKBackend Unit where
  -- ZKRepr : Type -> Type
  ZKRepr Unit := UInt32
  -- | Unit => UInt32

#check ZKBackend Unit
#check ZKBackend.ZKRepr Unit Unit
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
-- instance : ZKRepr1 Jolt UInt32 (ZKVar F128p) where


