
import ZkLean.AST
import ZkLean.Builder
import ZkLean.LookupTable
import ZkLean.Semantics

-- class Witnessable (f: Type) (t:Type) where
--   witness : ZKBuilder f t

-- Use Traversable instead??
class Encodable (t: Type) where
  ToZKExpr : Type

instance [JoltField f]: Encodable f where
  ToZKExpr := ZKExpr f
  -- witness := witnessf

instance [instA: Encodable a] [instB: Encodable b]: Encodable (a × b) where
  ToZKExpr := (instA.ToZKExpr × instB.ToZKExpr)
  -- witness := (<- witness, <- witness)

-- Implement Functor?

def run_circuit [JoltField f] (circuit: ZKBuilder f a) (state0: ZKBuilderState f) (witness: List f) : Bool :=
  let (_circ_output, final_state) := StateT.run circuit state0
  semantics witness final_state

-- def circuit_result [JoltField f] [oInst: Encodable o] (output: oInst.ToZKExpr) (state: ZKBuilderState f) (witness: List f) : o :=
--   let (circ_output, _final_state) := StateT.run (pure output) state
--   circ_output

-- def eval_expr [JoltField f] [aInst: Encodable a] (expr: aInst.ToZKExpr) (state: ZKBuilderState f) (witness: List f) : a :=
def eval_expr [JoltField f] (expr: ZKExpr f) (state: ZKBuilderState f) (witness: List f) : Option f :=
  let ram_values := semantics_ram witness state.ram_sizes state.ram_ops
  if let some ram_values := ram_values
  then 
    match semantics_zkexpr expr witness ram_values with
    | Value.VField f => some f
    | _ => none
  else
    none

def Hoare {f:Type} [JoltField f] [iInst: Encodable i] [oInst: Encodable o] (precondition: i -> Bool) (circuit: iInst.ToZKExpr -> ZKBuilder f oInst.ToZKExpr ) (postcondition: i -> o -> Bool) : Prop :=
  ∀ state0 : ZKBuilderState f, 
  ∀ witnesses : List f,
  ∀ input : i,
  ∀ output : o,
  ∀ input_expr : iInst.ToZKExpr,
  ∀ output_expr : oInst.ToZKExpr,
  -- ∀ x y : f,
  -- ∀ x_wit y_wit : WitnessId,
  -- ∀ _: x_wit < witnesses.length,
  -- ∀ _: y_wit < witnesses.length,
  -- -- let x_wit' : Nat := x_wit;
  -- -- witnesses.get? x_wit = some x →
  -- -- witnesses.get (((x_wit: WitnessId): ℕ): Fin witnesses.length) = x →
  -- witnesses[x_wit] = x →
  -- witnesses[y_wit] = y →
  eval_expr input_expr state0 witness = some input ->
  let statef := (StateT.run (circuit input_expr) state0).2
  eval_expr output_expr statef witness = some output ->

  precondition input →
    run_circuit (circuit input_expr) state0 witnesses ↔ postcondition input output -- x_expr y_expr

-- TODO: Will we need to prove that ZKExprs are immutable?
-- eval_expr expr state0 witness = eval_expr expr (StateT.run (circuit expr) state0).2 witness

