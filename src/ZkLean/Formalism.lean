
import Mathlib.Control.Traversable.Basic
import MPL

import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable
import ZkLean.Semantics

-- -- class Witnessable (f: Type) (t:Type) where
-- --   witness : ZKBuilder f t
-- 
-- -- Use this instead of Traversable??
-- class ZKEncodable (t: Type) where
--   ToZKExpr : Type
-- 
-- instance [JoltField f]: ZKEncodable f where
--   ToZKExpr := ZKExpr f
--   -- witness := witnessf
-- 
-- instance [instA: ZKEncodable a] [instB: ZKEncodable b]: ZKEncodable (a × b) where
--   ToZKExpr := (instA.ToZKExpr × instB.ToZKExpr)
--   -- witness := (<- witness, <- witness)

-- Implement Functor?

def run_circuit [JoltField f] (circuit: ZKBuilder f a) (state0: ZKBuilderState f) (witness: List f) : Bool :=
  let (_circ_output, final_state) := StateT.run circuit state0
  semantics witness final_state

def eval_circuit [JoltField f] (final_state: ZKBuilderState f) (witness: List f) : Prop :=
  semantics witness final_state

-- def circuit_result [JoltField f] [oInst: ZKEncodable o] (output: oInst.ToZKExpr) (state: ZKBuilderState f) (witness: List f) : o :=
--   let (circ_output, _final_state) := StateT.run (pure output) state
--   circ_output

-- def eval_expr [JoltField f] [aInst: ZKEncodable a] (expr: aInst.ToZKExpr) (state: ZKBuilderState f) (witness: List f) : a :=
def eval_exprf [JoltField f] (expr: ZKExpr f) (state: ZKBuilderState f) (witness: List f) : Option f :=
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops
  if let some ram_values := ram_values
  then 
    match semantics_zkexpr expr witness ram_values with
    | Value.VField f => some f
    | _ => none
  else
    none

def eval_expr {t: Type -> Type} [Traversable t] [JoltField f] (expr: t (ZKExpr f)) (state: ZKBuilderState f) (witness: List f) : Option (t f) :=
  traverse (eval_exprf · state witness) expr

-- def exec_circuit (circuit: i -> ZKBuilder f o) (input_expr: i) state0 := (StateT.run (circuit input_expr) state0).2

-- def Hoare (f:Type) (i:Type -> Type) (o:Type -> Type) [Traversable i] [Traversable o] [JoltField f] (precondition: i f -> Bool) (circuit: i (ZKExpr f) -> ZKBuilder f (o (ZKExpr f))) (postcondition: i f -> o f -> Bool) : Prop :=
--   ∀ state0 : ZKBuilderState f, 
--   ∀ witnesses : List f,
--   ∀ input : i f,
--   ∀ output : o f,
--   ∀ input_expr : i (ZKExpr f),
--   ∀ output_expr : o (ZKExpr f),
--   -- ∀ x y : f,
--   -- ∀ x_wit y_wit : WitnessId,
--   -- ∀ _: x_wit < witnesses.length,
--   -- ∀ _: y_wit < witnesses.length,
--   -- -- let x_wit' : Nat := x_wit;
--   -- -- witnesses.get? x_wit = some x →
--   -- -- witnesses.get (((x_wit: WitnessId): ℕ): Fin witnesses.length) = x →
--   -- witnesses[x_wit] = x →
--   -- witnesses[y_wit] = y →
--   eval_expr input_expr state0 witnesses = some input ->
--   let statef := (StateT.run (circuit input_expr) state0).2
--   eval_expr output_expr statef witnesses = some output ->
-- 
--   precondition input ->
--     run_circuit (circuit input_expr) state0 witnesses ↔ postcondition input output -- x_expr y_expr
-- 
-- -- TODO: Will we need to prove that ZKExprs are immutable?
-- -- eval_expr expr state0 witness = eval_expr expr (StateT.run (circuit expr) state0).2 witness
-- 
-- instance [Functor f1] [Functor f2] : Functor (λ t => f1 t × f2 t) where
--   map f x := match x with
--   | (a, b) => (f <$> a, f <$> b)
-- 
-- instance [Traversable f1] [Traversable f2] : Traversable (λ t => f1 t × f2 t) where
--   traverse f x := match x with
--     | (a, b) =>
--       (·,·) <$> traverse f a <*> traverse f b
-- 
-- def hoare_bind [Traversable i1] [Traversable o1] [Traversable i2] [Traversable o2] [Traversable i3] [Traversable o3] [JoltField f] :
--   Hoare f i1 o1 pre1 c1 post1 ->
--   Hoare f i2 o2 pre2 c2 post2 ->
--   forall input1: i1 f,
--   forall input2: i2 f,
--   forall _: (pre1 input1 && pre2 input2 -> pre3 (input1, input2)),
--   forall output1: o1 f,
--   Hoare f (λ t => i1 t × i2 t) o2 pre3 (λ (in1, in2) => do
--       let _ <- c1 in1
--       c2 in2
--     ) (λ (in1, in2) out2 => post1 in1 output1 && post2 in2 out2) := by
--   sorry

lemma failure_propagates [JoltField f] (m : ZKBuilder f a) (witness: List f) :
 -- TODO: Lawful m
 ⦃λ s => s = s0⦄
 m
 ⦃⇓_r s1 => ⌜ ¬(eval_circuit s0 witness) → ¬(eval_circuit s1 witness)⌝⦄
 := by
  sorry

lemma previous_success [JoltField f] (m : ZKBuilder f a) (witness: List f) :
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


