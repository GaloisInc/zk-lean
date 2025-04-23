
import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable
import ZkLean.Semantics

def run_circuit [JoltField f] (circuit: ZKBuilder f a) (state0: ZKBuilderState f) (witness: List f) : Bool :=
  let (_circ_states, zk_builder) := StateT.run circuit state0
  let b := semantics_constraints zk_builder.constraints witness (Array.empty)
  b


def Hoare (f:Type) [JoltField f] (precondition: f -> f -> Bool) (circuit: ZKExpr f -> ZKExpr f -> ZKBuilder f a) (postcondition: f -> f -> Bool) : Prop :=
  ∀ witnesses : List f,
  ∀ state0 : ZKBuilderState f, 
  ∀ x y : f,
  ∀ x_wit y_wit : WitnessId,
  ∀ _: x_wit < witnesses.length,
  ∀ _: y_wit < witnesses.length,
  -- let x_wit' : Nat := x_wit;
  -- witnesses.get? x_wit = some x →
  -- witnesses.get (((x_wit: WitnessId): ℕ): Fin witnesses.length) = x →
  witnesses[x_wit] = x →
  witnesses[y_wit] = y →

  precondition x y →
   run_circuit (circuit (ZKExpr.WitnessVar x_wit) (ZKExpr.WitnessVar y_wit)) state0 [x, y] ↔ postcondition x y -- x_expr y_expr

