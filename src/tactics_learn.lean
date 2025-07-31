import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

import Lean

abbrev ff := 4139
abbrev f := ZMod ff
abbrev b := Nat.log2 ff




open Lean Elab Tactic Meta

partial def pushValInsideWithProof (e : Expr) : MetaM (Expr × Expr) := do
  logInfo m!"😊 Expression: {e} : {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``ZMod.val, #[modulus, sumExpr]) =>
    --logInfo m!"😊 Expression: {modulus} : {sumExpr}"
    match sumExpr.getAppFnArgs with
    | (``HAdd.hAdd, args) => do
      match args.toList.reverse with
        | y :: x :: _ => do
             let (x', pf1)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[x])
             let (y', pf2)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[y])
             let zx ← mkAppM ``ZMod.val #[x]
             let zy ← mkAppM ``ZMod.val #[y]
             let sum1 ← mkAppM ``HAdd.hAdd #[zx, zy]
             logInfo m!"{sum1}"


            -- x' + ZMod.val y
             let tx ← inferType zx
             let xVar ← mkFreshExprMVar tx
             let f1 ← mkLambdaFVars #[xVar] (← mkAppM ``HAdd.hAdd #[xVar, zy])
             logInfo m!"{f1}"
             let pf1' ← mkCongrArg f1 pf1
             logInfo m!"{pf1'}"

            -- x' + y'
             let ty ← inferType zy
             let yVar ← mkFreshExprMVar zy
             let f2 ← mkLambdaFVars #[yVar] (← mkAppM ``HAdd.hAdd #[yVar, zy])
             let pf2' ← mkCongrArg f2 pf2
             let pfAdd ← mkEqTrans pf1' pf2' -- ZMod.val x + ZMod.val y = x' + y'


             let sum2 ← mkAppM ``HAdd.hAdd #[x', y']
             let mod1 ← mkAppM ``HMod.hMod #[sum1, modulus]
             let mod2 ← mkAppM ``HMod.hMod #[sum2, modulus]

            -- modFn : (n : ℕ) ↦ n % modulus
             let modFn ← mkLambdaFVars #[sum2] (← mkAppM ``HMod.hMod #[sum2, modulus])
             let pfMod ← mkCongrArg modFn pfAdd

             let base ← mkAppM ``ZMod.val_add #[x, y]
             let full ← mkEqTrans base pfMod
             logInfo m!"{mod2}"
             logInfo m!"{full}"

             return (mod2, full)

                     -- Apply congrArg₂ to base: rewrite RHS using pf1 and pf2
             --logInfo m!"📌 Base: {← ppExpr base}"
             --logInfo m!"😊 Adding {x} and {y}"
             --return (rhs,base)
        | _ =>
          let eqType ← mkEq e e
          let refl ← mkAppM ``Eq.refl #[e]
          return (e, refl)
    | _ =>
          logInfo m!"We are here"
          let eqType ← mkEq e e
          let refl ← mkAppM ``Eq.refl #[e]
          logInfo m!"{refl}, {e}"
          return (e, refl)
  | _ => return (e, ← mkEqRefl e)
  --   | (``HMul.hMul, args) => do
  --     match args.toList.reverse with
  --       | y :: x :: _ => do
  --            let (x', pf1)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[x])
  --            let (y', pf2)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[y])
  --            let sum ← mkAppM ``HMul.hMul #[x', y']
  --            let rhs ← mkAppM ``HMod.hMod #[sum, modulus]
  --            let base ← mkAppM ``ZMod.val_mul #[x, y]
  --            logInfo m!"📌 Base: {← ppExpr base}"
  --            --logInfo m!"😊 Adding {x} and {y}"
  --            return (rhs,base)
  --       | _ => return (e, e)
  --   | _ => return (e, e)
  -- | _ => return (e, e)




  -- Now h is rewritten to:
  -- (((ZMod.val x + ZMod.val y) % 17 + ZMod.val z) % 17 = 5)
open Lean Meta Elab Tactic

open Lean Meta Elab Tactic





-- open Lean Elab Tactic



/-- helper function: recurse into a `ZMod.val expr`, returning the rewritten form + proof -/




elab "val_add_rec" : tactic => do
  let goal ← getMainGoal
  let tgt ← getMainTarget
  match tgt.eq? with
  | some (_, lhs, rhs) => do
    let (lhs', pf) ← pushValInsideWithProof lhs
    let final ← mkEqTrans pf (← mkEqRefl rhs)
    goal.assign final
    setGoals [goal]
  | none => throwError "Goal is not an equality"



--- Tests
-- example (a b c d : ZMod 17) :
--   (a + b).val = (a.val + b.val) % 17 := by
--   val_add_rec

-- example (a b c d : ZMod 17) :
--   (( a + b + c) * d).val = (((((a.val + b.val) % 17 + c.val) % 17 )* d.val) % 17) := by
--   val_add_rec


-- example (x y z : ZMod 17) (h: y.val <= x.val ) :
--   ((x- y)*z).val = ( (x.val - y.val) * z.val ) %17 := by
--   val_add_rec


--   apply Eq.trans (ZMod.val_mul (x - y) z)
--   apply congrArg (fun a => a * z.val % 17) (ZMod.val_sub _)
--   -- Apply function to both sides


-- example (y z: ZMod 11) :
--   (1- y).val = (1 - y.val) := by
--   trivial


-- example (y z: ZMod 11) (h: y.val <= 1) :
--   (1- y).val = (1 - y.val) := by
--   rw [ZMod.val_sub]
--   rw [ZMod.val_one]

-- Next Steps:
-- how do we propagate range analysis
elab "dump_named_hyps" hname:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    let targetName := hname.getId
    let some decl := lctx.findFromUserName? targetName
      | throwError m!"Could not find a hypothesis named `{targetName}`"
    logInfo m!"📌 {decl.userName} : {decl.type}"

example (x y z : ZMod 17) :
  (((x + y) + z).val = 5 → x.val + y.val + z.val = 5) := by
  intros h
  dump_named_hyps h
