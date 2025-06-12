import Mathlib.Control.Traversable.Basic
import MPL

import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable
import ZkLean.Semantics

open ZKBuilder            -- brings the smart constructors into scope

/-- Run a circuit‑building *program* and then evaluate the resulting circuit. -/
def run_circuit [ZKField f]
    (prog    : ZKBuilder f a)
    (state₀  : ZKBuilderState f)
    (witness : List f) : Bool :=
  -- `build` interprets the free‑monad program into a final state.
  let (_out, state₁) := build prog state₀
  semantics witness state₁

/-- Evaluate a previously‑built circuit (represented only by its final state). -/
def eval_circuit [ZKField f]
    (state   : ZKBuilderState f)
    (witness : List f) : Prop :=
  semantics witness state

/-- Evaluate a single expression inside an existing circuit state. -/
def eval_exprf [ZKField f]
    (e       : ZKExpr f)
    (state   : ZKBuilderState f)
    (witness : List f) : Option f :=
  match semantics_ram witness state.ram_sizes state.ram_ops with
  | some ram_values => semantics_zkexpr e witness ram_values
  | none            => none

/-- Evaluate all expressions in a traversable container. -/
def eval_traversable_expr
    {t : Type → Type} [Traversable t] [ZKField f]
    (es      : t (ZKExpr f))
    (state   : ZKBuilderState f)
    (witness : List f) : Option (t f) :=
  traverse (fun e => eval_exprf e state witness) es

-- /-- If a circuit fails at a given state then it must fail for subsequent state. -/
-- lemma failure_propagates [ZKField f] (m : ZKBuilder f a) (witness: List f) :
--  -- TODO: Lawful m
--  ⦃λ s => s = s0⦄
--  m
--  ⦃⇓_r s1 => ⌜ ¬(eval_circuit s0 witness) → ¬(eval_circuit s1 witness)⌝⦄
--  := by
--   sorry

-- /-- If a circuit succeeds at a given state then it must have succeeded in previous state. -/
-- lemma previous_success [ZKField f] (m : ZKBuilder f a) (witness: List f) :
--  -- TODO: Lawful m
--  ⦃λ s => s = s0⦄
--  m
--  ⦃⇓_r s1 => ⌜eval_circuit s1 witness → eval_circuit s0 witness⌝⦄
--  := by
--   sorry

-- /-- If an expression evaluates to a value at a given state then it must evaluate at the same value for a subsequent state. -/
-- lemma eval_const [ZKField f] (m : ZKBuilder f a) (witness: List f) (expr: ZKExpr f) :
--  -- TODO: Lawful m
--  ⦃λ s => s = s0⦄
--  m
--  ⦃⇓_r s1 => ⌜eval_exprf expr s0 witness = eval_exprf expr s1 witness⌝⦄
--  := by
--   sorry
