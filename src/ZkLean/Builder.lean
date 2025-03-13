import Std.Data.HashMap.Basic
import ZkLean.AST
import ZkLean.LookupTable

structure ZKBuilderState (f:Type) where
  foo: Bool
  -- environment: Std.HashMap Ident (ZKExpr f)
  allocated_witness_count: Nat
  constraints: List (ZKExpr f)
deriving instance Inhabited for ZKBuilderState

  -- TODO: environment? AST?

-- ZKRepr ??
-- ZKRepr Jolt u32 = F128p

-- TODO: Make this a free monad?
def ZKBuilder (f:Type) := StateM (ZKBuilderState f)

instance: Monad (ZKBuilder f) where
  pure := sorry
  bind := sorry

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
def witness [Inhabited f] [Inhabited a] : ZKBuilder f a := do
  -- TODO
  -- allocate the wires necessary for `a`
  sorry

def witnessf : ZKBuilder f (ZKExpr f) := do
  /-let old_count <- StateT.modifyGet
    (fun old_state =>
      let (p :Nat) := old_state.allocated_wire_count
      (p, {old_state with allocated_wire_count := p + 1 })
    )
    -/
  let old_state <- StateT.get
  let old_count := old_state.allocated_witness_count
  let new_count := old_count +1
  StateT.set { old_state with allocated_witness_count := new_count}
  pure (ZKExpr.WitnessVar old_count)



def constrain (_constraint: ZKExpr f) : ZKBuilder f PUnit :=
  -- TODO
  sorry

def constrainEq (x: ZKExpr f) (y: ZKExpr f) : ZKBuilder f PUnit :=
  constrain (ZKExpr.Eq x y)

def constrainR1CS (a: ZKExpr f) (b: ZKExpr f) (c: ZKExpr f) : ZKBuilder f PUnit :=
  constrainEq (ZKExpr.Mul a b) c


def lookupSubtable (_table : Subtable f n) (a: ZKExpr f) (_:ZKExpr f) : ZKBuilder f (ZKExpr f) :=
  let () := panic "TODO"
  pure a


def lookup (_table : ComposedLookupTable f n c) (_a: ZKExpr f) (_a: ZKExpr f) [Inhabited f] : ZKBuilder f (ZKExpr f) :=
  let () := panic "TODO"
  pure _a
