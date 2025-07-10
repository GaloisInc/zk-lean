import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

import Lean

abbrev ff := 4139
abbrev f := ZMod ff
abbrev b := Nat.log2 ff




open Lean Elab Tactic Meta

partial def pushValInsideWithProof (e : Expr) : MetaM (Expr × Expr) := do
  --logInfo m!"😊 Expression: {e} : {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``ZMod.val, #[modulus, sumExpr]) =>
    logInfo m!"😊 Expression: {modulus} : {sumExpr}"
    match sumExpr.getAppFnArgs with
    | (``HAdd.hAdd, args) => do
      match args.toList.reverse with
        | y :: x :: _ => do
             let (x', pf1)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[x])
             let (y', pf1)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[y])
             let ff ← mkConstWithFreshMVarLevels ``ff
             let sum ← mkAppM ``HAdd.hAdd #[x', y']
             let rhs ← mkAppM ``HMod.hMod #[sum, ff]
             let base ← mkAppM ``ZMod.val_add #[x, y]
             logInfo m!"😊 Adding {x} and {y}"
             return (rhs,base)
        | _ => return (e, e)
    | _ => return (e, e)
  | _ => return (e, e)
  --   match zExpr.getAppFnArgs with
  --   | (``HAdd.hAdd, #[_, _, x, y]) => do
  --       let (x', pf1) ← pushValInsideWithProof (← mkAppM ``ZMod.val #[x])
  --       let (y', pf2) ← pushValInsideWithProof (← mkAppM ``ZMod.val #[y])
  --       let ff ← mkConstWithFreshMVarLevels ``ff
  --       let sum ← mkAppM ``HAdd.hAdd #[x', y']
  --       let rhs ← mkAppM ``HMod.hMod #[sum, ff]
  --       let base ← mkAppM ``ZMod.val_add #[x, y]
  --       --let eq₁ ← mkEq e (← mkAppM ``HMod.hMod #[← mkAppM ``HAdd.hAdd #[← mkAppM ``ZMod.val #[x], ← mkAppM ``ZMod.val #[y]], ff])
  --      -- let step₁ ← mkEqTrans base (← mkEqRefl rhs)
  --       return (rhs, base)
  --   | _ => return (e, ← mkEqRefl e)
  -- | _ => return (e, ← mkEqRefl e)



elab "rewrite_val_in_hyp" hname:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    let targetName := hname.getId
    let some decl := lctx.findFromUserName? targetName
      | throwError m!"Could not find a hypothesis named `{targetName}`"
    logInfo m!"📌 {decl.userName} : {decl.type}"
    let type ← instantiateMVars decl.type
    match Lean.Expr.eq? type with
      | some (_, lhsExpr, rhsExpr) => do
        logInfo m!"📌 Original hypothesis: {← ppExpr type}"
        logInfo m!"📌 Lhs: {← ppExpr lhsExpr}"
        let (lhsRewritten, pf) ← pushValInsideWithProof lhsExpr
        logInfo m!"📌 New: {← ppExpr lhsRewritten}"
        logInfo m!"📌 Proof: {← ppExpr pf}"
        let newEq ← mkEq lhsRewritten rhsExpr
        let pfSymm ← mkEqSymm pf
        let newProof ← mkEqTrans pfSymm decl.toExpr
        let fvarIdNew ← mvarId.assert decl.userName newEq newProof
        let fvarId := decl.fvarId
        let newGoal ← mvarId.replaceLocalDecl fvarId pfSymm  newProof
        replaceMainGoal [newGoal.mvarId]
      | none => throwError "Hypothesis {hname} is not an equality"


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
  rewrite_val_in_hyp h

  --intros h
  --rewrite_val_in_hyp h



  -- Now h is rewritten to:
  -- (((ZMod.val x + ZMod.val y) % 17 + ZMod.val z) % 17 = 5)
