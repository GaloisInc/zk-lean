
import Mathlib.Control.Traversable.Basic
--import Std.Do
import MPL
import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable
import ZkLean.Semantics

/-- Run a circuit builder given an initial builder state and then evaluate the resulting circuit given witnesses. -/
def run_circuit [ZKField f] (circuit: ZKBuilder f a) (state0: ZKBuilderState f) (witness: List f) : Bool :=
  let (_circ_output, final_state) := runFold circuit state0
  semantics witness final_state

/-- Evaluate a circuit given some witnesses and a builder final state. -/
def eval_circuit [ZKField f] (final_state: ZKBuilderState f) (witness: List f) : Prop :=
  semantics witness final_state

/-- Evaluate an expression given a builder state and some witnesses. -/
def eval_exprf [ZKField f] (expr: ZKExpr f) (state: ZKBuilderState f) (witness: List f) : Option f :=
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops
  if let some ram_values := ram_values
  then
    semantics_zkexpr expr witness ram_values
  else
    none

def eval_traversable_expr {t: Type -> Type} [Traversable t] [ZKField f] (expr: t (ZKExpr f)) (state: ZKBuilderState f) (witness: List f) : Option (t f) :=
  traverse (eval_exprf · state witness) expr

open MPL
--open Std.Do
/-- If a circuit fails at a given state then it must fail for subsequent state. -/
lemma failure_propagates [ZKField f] (m : ZKBuilder f a) (witness: List f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜ ¬(eval_circuit s0 witness) → ¬(eval_circuit s1 witness)⌝⦄
 := by
  sorry
/-- If a circuit succeeds at a given state then it must have succeeded in previous state. -/
lemma previous_success [ZKField f] (m : ZKBuilder f a) (witness: List f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜eval_circuit s1 witness → eval_circuit s0 witness⌝⦄
 := by
  sorry

/-- If an expression evaluates to a value at a given state then it must evaluate at the same value for a subsequent state. -/
lemma eval_const [ZKField f] (m : ZKBuilder f a) (witness: List f) (expr: ZKExpr f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜eval_exprf expr s0 witness = eval_exprf expr s1 witness⌝⦄
 := by
  sorry
