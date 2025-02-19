import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable

structure ZKBuilderState: Type u where
  foo: Bool
  -- environment: Std.HashMap Ident (ZKExpr f)
  -- constraints: List (ZKExpr f)

  -- TODO: environment? AST?

-- ZKRepr ??
-- ZKRepr Jolt u32 = F128p

-- TODO: Make this a free monad?
def ZKBuilder := StateM ZKBuilderState
deriving instance Monad for ZKBuilder
-- structure ZKBuilder (a: Type) where
--   runBuilder: ZKBuilderState -> (a, ZKBuilderState)

-- instance : Monad ZKBuilder where
--   pure _x :=
--     {
--       environment := Std.HashMap.empty,
--     } -- TODO
--   bind _opt _next :=
--     {
--       environment := Std.HashMap.empty,
--     } -- TODO

-- def witness {t : Type} : ZKBuilder (ZKExpr t) :=
def witness {a : Type u} [Inhabited a] : ZKBuilder a := do
  -- TODO
  pure (panic "TODO")


def constrain (_constraint: ZKExpr f) : ZKBuilder PUnit :=
  pure (panic "TODO")

def constrainEq (x: ZKExpr f) (y: ZKExpr f) : ZKExpr Bool :=
  ZKExpr.Eq x y
infix:50    " === " => constrainEq


def lookupSubtable (_table : Subtable f n) (a: ZKExpr f) (_:ZKExpr f) : ZKBuilder (ZKExpr f) :=
  let () := panic "TODO"
  pure a


def lookup (_table : ComposedLookupTable f n c) (_a: ZKExpr f) (_a: ZKExpr f) [Inhabited f] : ZKBuilder (ZKExpr f) :=
  let () := panic "TODO"
  pure _a
