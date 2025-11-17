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
