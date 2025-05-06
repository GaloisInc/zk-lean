
import Mathlib.Control.Traversable.Basic
import MPL

import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable
import ZkLean.Semantics

def run_circuit [JoltField f] (circuit: ZKBuilder f a) (state0: ZKBuilderState f) (witness: List f) : Bool :=
  let (_circ_output, final_state) := StateT.run circuit state0
  semantics witness final_state

def eval_circuit [JoltField f] (final_state: ZKBuilderState f) (witness: List f) : Prop :=
  semantics witness final_state

def eval_exprf [JoltField f] (expr: ZKExpr f) (state: ZKBuilderState f) (witness: List f) : Option f :=
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops
  if let some ram_values := ram_values
  then 
    semantics_zkexpr expr witness ram_values
  else
    none

def eval_traversable_expr {t: Type -> Type} [Traversable t] [JoltField f] (expr: t (ZKExpr f)) (state: ZKBuilderState f) (witness: List f) : Option (t f) :=
  traverse (eval_exprf · state witness) expr

lemma failure_propagates [JoltField f] (m : ZKBuilder f a) (witness: List f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜ ¬(eval_circuit s0 witness) → ¬(eval_circuit s1 witness)⌝⦄
 := by
  sorry

lemma previous_success [JoltField f] (m : ZKBuilder f a) (witness: List f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜eval_circuit s1 witness → eval_circuit s0 witness⌝⦄
 := by
  sorry

lemma eval_const [JoltField f] (m : ZKBuilder f a) (witness: List f) (expr: ZKExpr f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜eval_exprf expr s0 witness = eval_exprf expr s1 witness⌝⦄
 := by
  sorry


