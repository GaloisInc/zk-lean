import Mathlib.Algebra.Field.Defs
import Mathlib.Control.Fold
import ZkLean

def main : IO Unit :=
  IO.println s!"Hello!"




-- ZKProof 7 examples

def example1 [JoltField f] : ZKBuilder f (ZKExpr f) := do
  let x: ZKExpr f <- Witnessable.witness
  let one: ZKExpr f := 1
  constrain (x * (x - one) === 0)
  return x

def eq8 [Field f] : Subtable f 16 :=
  let product v := Traversable.foldl (. * .) 1 v.toList
  let first_half (v: Vector _ 16) : Vector _ 8 := Vector.take v 8
  let second_half (v: Vector _ 16) : Vector _ 8 := Vector.drop v 8
  let mle_on_pair a b:= product (Vector.zipWith a b (λ x y => (x * x + (1 - x) * (1 - y))))
  let mle (v: Vector f 16): f := mle_on_pair (first_half v) (second_half v)
  subtableFromMLE mle

def eq32 [Field f] : ComposedLookupTable f 16 4 :=
  mkComposedLookupTable
    #[ (eq8, 0), (eq8, 1), (eq8, 2), (eq8, 3) ].toVector
    (fun results => results.foldl (· * ·) 1)

structure RISCVState (f: Type) where
  pc: ZKExpr f
  registers: Vector (ZKExpr f) 32
deriving instance Inhabited for RISCVState

instance: Witnessable f (RISCVState f) where
  witness := do
   let pc <- Witnessable.witness
   let registers <- Witnessable.witness
   pure { pc:=pc, registers := registers}

-- TODO: define a type class function for `witness` to return RISCVState

def step [JoltField f] (prev_st : RISCVState f) : ZKBuilder f (RISCVState f) := do
  let new_st: RISCVState f <- Witnessable.witness -- allocate a wire for witness

  let r1 := prev_st.registers[1]
  let r2 := prev_st.registers[2]

  let isEq <- lookup eq32 r1 r2
  constrain (new_st.registers[0] === isEq)

  return new_st


def rv_circ [JoltField f]: ZKBuilder f (List (RISCVState f))  := do
  let (init_state : RISCVState f) <- Witnessable.witness -- fix this
  let (state1 : RISCVState f) <- step init_state
  let (state2 : RISCVState f) <- step state1
  let (state3 : RISCVState f) <- step state2
  pure [init_state, state1, state2, state3]

#check rv_circ

inductive Value (f: Type) [JoltField f] where
  | VBool : Bool -> Value f
  | VField : f -> Value f
  | None : Value f

def semantics_zkexpr [JoltField f] (exprs: ZKExpr f) (witness: List f ) : Value f :=
  let rec eval (e: ZKExpr f) : Value f :=
    match e with
    | ZKExpr.Literal lit => Value.VField lit
    | ZKExpr.WitnessVar id =>
      if compare id (witness.length : WitnessId) == Ordering.lt
      then Value.VField (witness.get! id)
      else Value.None
    | ZKExpr.Add lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va + vb)
      | _, _ => Value.None
    | ZKExpr.Sub lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va - vb)
      | _, _ => Value.None
    | ZKExpr.Mul lhs rhs =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb => Value.VField (va * vb)
      | _, _ => Value.None
    | ZKExpr.Eq lhs rhs  =>
      let a := eval lhs
      let b := eval rhs
      match a,b with
      | Value.VField va, Value.VField vb =>
        let b: Bool := va == vb
        Value.VBool b
      | _, _ => Value.None
  eval exprs

def constraints_semantics [JoltField f] (constraints: List (ZKExpr f)) (witness: List f ) : Bool :=
  match constraints with
  | [] => true
  | c :: cs =>
    let sem_c := semantics_zkexpr c witness
    match sem_c with
    | Value.VBool b =>
      if b
      then constraints_semantics cs witness
      else false
    | _ => false

def run_circ [JoltField f] (witness: List f) : Bool :=
  let (_circ_states, zk_builder) := StateT.run (rv_circ (f := f)) default
  let b := constraints_semantics zk_builder.constraints witness
  b


-- structure RISCVState (backend: Type) where
--   pc: ZKRepr backend UInt32
--   registers: Vector (ZKRepr backend UInt32) 32

-- structure RISCVState (backend: Type) [c: ZKBackend backend] where
--   pc: ZKRepr backend
--   registers: Vector (ZKRepr backend) 32

-- inductive RISCVState backend [c: ZKBackend backend] where
-- -- | MkRISCVState : ZKRepr -> Vector ZKRepr 1 -> RISCVState backend
-- | MkRISCVState : ZKRepr -> List ZKRepr -> RISCVState backend
--
-- def test : RISCVState Jolt := RISCVState.MkRISCVState 1 [1]

-- structure RISCVState (backend : Type) where
--   pc: ZKRepr backend Unit
--   -- registers: List (zkrepr UInt32)

-- #check RISCVState.mk 32

-- structure [ZKRepr zkrepr] RISCVState (zkrepr : Type) where
--   pc: repr zkrepr UInt32
--   -- registers: List (zkrepr UInt32)

-- def example2 {zkrepr:Type} [ZKRepr1 zkrepr Unit Unit] : ZKBuilder (RISCVState (ZKRepr1 zkrepr Unit)) := do
-- def example2 {zkrepr:Type} : ZKBuilder (RISCVState zkrepr) := do
--   let new_st <- witness
--
--   pure new_st


-- #eval example1

-- #check -5
-- #check (Int.natAbs) -5




-- Jolt examples

def eqSubtable [JoltField f] : Subtable f 2 := subtableFromMLE (λ x => (x[0] * x[1] + (1 - x[0]) * (1 - x[1])))

-- forall x y : F . 0 <= x < 2^n && 0 <= y < 2^n => eqSubtable (bits x) (bits y) == (toI32 x == toI32 y)


structure JoltR1CSInputs (f : Type 0):  Type 1 where
  chunk_1: ZKExpr f
  chunk_2: ZKExpr f
  /- ... -/

-- A[0] = C * 1 + var[3] * 829 + ...
-- Example of what we extract from Jolt
-- TODO: Make a struct for the witness variables in a Jolt step. Automatically extract this from JoltInputs enum?
def uniform_jolt_constraint [JoltField f] (jolt_inputs: JoltR1CSInputs f) : ZKBuilder f PUnit := do
  constrainR1CS ((1 +  jolt_inputs.chunk_1 ) * 829) 1 1
  constrainR1CS 1 1 ((1 +  jolt_inputs.chunk_1 ) * 829)
  -- ...

--   ...
-- def non_uniform_jolt_constraint step_1 step_2 = do
--   constrainR1CS (step_1.jolt_flag * 123) (step_2.jolt_flag + 1) (1)
--   constrainR1CS (step_1.jolt_flag * 872187687 + ...) (step_2.jolt_flag + 1) (1)
--   ...
