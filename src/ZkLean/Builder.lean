
import Std.Data.HashMap.Basic

import ZkLean.AST
import ZkLean.LookupTable

structure ZKBuilderState where
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
def witness {a : Type} [Inhabited a] : ZKBuilder a := do
  -- TODO
  pure (panic "TODO")


def constrain (_constraint: ZKBuilder Bool) : ZKBuilder Unit :=
  pure (panic "TODO")

def constrainEq (_x: ZKExpr a) (_y: ZKExpr a) : ZKBuilder Bool :=
  pure (panic "TODO")
infix:50    " === " => constrainEq


def lookup (_table : LookupTable f) (_:ZKExpr f) (_:ZKExpr f) [Inhabited f] : ZKBuilder (ZKExpr f) :=
  let e := panic "TODO"
  pure e
