import Mathlib.Control.Traversable.Basic
import Std.Do

import ZKLean.AST
import ZKLean.Builder
import ZKLean.LookupTable
import ZKLean.Semantics

/-- Run a circuit builder given the witness and then evaluate the resulting circuit. -/
@[simp_ZKSemantics]
def run_circuit [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Bool :=
  semantics circuit witness

/-- Evaluate a circuit given some witnesses and a builder final state. -/
@[simp_ZKSemantics]
def eval_circuit [ZKField f] (circuit: ZKBuilder f a) (witness: List f) : Prop :=
  semantics circuit witness

open Std.Do

/-- `ZKBuilder` admits a weakest‐precondition interpretation in terms of the
`MPL` predicate–transformer semantics.  A builder computation manipulates an
implicit `ZKBuilderState`; therefore its predicate shape is `PostShape.arg
(ZKBuilderState f) .pure`.

The interpretation simply executes the computation with `runFold_old` and feeds the
result to the post-condition. -/


@[simp_ZKBuilder]
-- instance [Zero f] : WP (ZKBuilder f) (.arg (ZKState f) .pure) where
instance [ZKField f] : WP (ZKBuilder f) (.arg (ZKState f) (.except PUnit .pure)) where
  wp {α} (x : ZKBuilder f α) :=
    PredTrans.pushArg (fun s =>
      PredTrans.pushExcept (
        match runFold x s with
        | .some r => ExceptT.mk (PredTrans.pure (Except.ok r))
        | .none => ExceptT.mk (PredTrans.pure (Except.error ()))
      )
    )
  -- wp {α} (x : ZKBuilder f α) :=
  --   -- We reuse the `StateT` instance for predicate transformers: run the
  --   -- builder starting from an initial state and hand the resulting
  --   -- `(value, state)` pair to the post-condition.
  --   PredTrans.pushArg (fun s =>
  --     PredTrans.pure (runFold x s))

@[simp_ZKSemantics]
lemma expr_immutable [ZKField f] (c: ZKBuilder f α) (e: ZKExpr f) (ef: f) :
  ⦃λ s => ⌜ e.eval = some ef ⌝ ⦄
  c
  ⦃λ _r s => ⌜ e.eval = some ef ⌝ ⦄
  -- ⦃λ (_r: Unit) (s : ZKState f) => ⌜ True ⌝ ⦄ -- s.eval_expr e = some ef ⌝ ⦄
  := sorry

-- /-- Evaluate an expression given a builder state and some witnesses. -/
-- @[simp_ZKSemantics]
-- def eval_exprf [ZKField f] (expr: ZKExpr f) (state: ZKBuilderState f) (witness: List f) : Option f :=
--   let ram_values := semantics_ram witness state.ram_sizes state.ram_ops
--   if let some ram_values := ram_values
--   then
--     semantics_zkexpr expr witness ram_values
--   else
--     none
-- 
-- @[simp_ZKSemantics]
-- def eval_traversable_expr {t: Type -> Type} [Traversable t] [ZKField f] (expr: t (ZKExpr f)) (state: ZKBuilderState f) (witness: List f) : Option (t f) :=
--   traverse (eval_exprf · state witness) expr
-- 
-- open Std.Do
-- 
-- /-- If a circuit fails at a given state then it must fail for subsequent state. -/
-- lemma failure_propagates [ZKField f] (m : ZKBuilder f a) (witness: List f) s0 :
--  -- TODO: Lawful m
--  ⦃λ s => ⌜s = s0⌝⦄
--  m
--  ⦃⇓_r s1 => ⌜¬(eval_circuit s0 witness) → ¬(eval_circuit s1 witness)⌝⦄
--  := by
--   sorry
-- 
-- /-- If a circuit succeeds at a given state then it must have succeeded in previous state. -/
-- lemma previous_success [ZKField f] (m : ZKBuilder f a) (witness: List f) :
--  -- TODO: Lawful m
--  ⦃λ s => ⌜s = s0⌝⦄
--  m
--  ⦃⇓_r s1 => ⌜eval_circuit s1 witness → eval_circuit s0 witness⌝⦄
--  := by
--   sorry
-- 
-- /-- If an expression evaluates to a value at a given state then it must evaluate at the same value for a subsequent state. -/
-- lemma eval_const [ZKField f] (m : ZKBuilder f a) (witness: List f) (expr: ZKExpr f) :
--  -- TODO: Lawful m
--  ⦃λ s => ⌜s = s0⌝⦄
--  m
--  ⦃⇓_r s1 => ⌜eval_exprf expr s0 witness = eval_exprf expr s1 witness⌝⦄
--  := by
--   sorry

/--
The following machinery is not needed to prove properties about circuits in zkLean, but they may be useful to prove completeness.
-/
class CircuitInput (i: Type) (f: Type) [ZKField f] where
  -- /-- Circuit representation of input i. For example, the circuit representation of `f` might be `ZKExpr f`. -/
  -- CircuitInputRepr : Type

  /-- Function that generates the extended witness from the input to a circuit. -/
  witness_generation : i → List f -- JP: Does a `Writer` make more sense?

/-- Proposition that states that a circuit is sound with respect to a specification. -/
def sound [ZKField f] (circuit: input_exprs → ZKBuilder f α) (specification : ZKState f → input_exprs → α → Prop) : input_exprs → Prop :=
  λ inputs => 
  ⦃ λ s => ⌜ true ⌝ ⦄
  circuit inputs
  ⦃ λ output s => ⌜ specification s inputs output ⌝ ⦄
  -- semantics circuit extended_witness → specification inputs

/-- Proposition that states that a circuit is complete with respect to a specification. -/
def complete [ZKField f] [I: CircuitInput i f] (circuit: ZKBuilder f α) (preconditions : i → Prop) : i → Prop :=
  λ inputs =>
    let extended_witness := I.witness_generation inputs
    preconditions inputs → semantics circuit extended_witness
