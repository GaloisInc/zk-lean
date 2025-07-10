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
    --logInfo m!"😊 Expression: {modulus} : {sumExpr}"
    match sumExpr.getAppFnArgs with
    | (``HAdd.hAdd, args) => do
      match args.toList.reverse with
        | y :: x :: _ => do
             let (x', pf1)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[x])
             let (y', pf2)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[y])
             let sum ← mkAppM ``HAdd.hAdd #[x', y']
             let rhs ← mkAppM ``HMod.hMod #[sum, modulus]
             let base ← mkAppM ``ZMod.val_add #[x, y]
                     -- Apply congrArg₂ to base: rewrite RHS using pf1 and pf2

             logInfo m!"📌 Base: {← ppExpr base}"
             --logInfo m!"😊 Adding {x} and {y}"
             return (rhs,base)
        | _ => return (e, e)
    | (``HMul.hMul, args) => do
      match args.toList.reverse with
        | y :: x :: _ => do
             let (x', pf1)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[x])
             let (y', pf2)  ← pushValInsideWithProof (← mkAppM ``ZMod.val #[y])
             let sum ← mkAppM ``HMul.hMul #[x', y']
             let rhs ← mkAppM ``HMod.hMod #[sum, modulus]
             let base ← mkAppM ``ZMod.val_mul #[x, y]
             logInfo m!"📌 Base: {← ppExpr base}"
             --logInfo m!"😊 Adding {x} and {y}"
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


-- (x + y + z).val --> ((x.val + y.val) % ff + z.val) % ff



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
        let (lhsRewritten, pf) ← pushValInsideWithProof lhsExpr
        let newEq ← mkEq  lhsRewritten lhsExpr
        logInfo m!"📌 hypothesis: {← ppExpr newEq}"
        logInfo m!" proof {← ppExpr pf}"
        let result ← mvarId.assertAfter decl.fvarId `h_named newEq pf
        --let (fvarId, mvarId'') ← mvarId'.intro1 #[fvarId]
        replaceMainGoal [result.mvarId]

      | none => throwError "Hypothesis {hname} is not an equality"

elab "rewrite_val_in_goal" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    let type <- mvarId.getType
    match Lean.Expr.eq? type with
      | some (_, lhsExpr, rhsExpr) => do
        let (lhsRewritten, pf) ← pushValInsideWithProof lhsExpr
        let newEq ← mkEq  lhsRewritten lhsExpr
        logInfo m!"📌 hypothesis: {← ppExpr newEq}"
        logInfo m!" proof {← ppExpr pf}"
        let fvarId ← mkFreshFVarId
        let result ← mvarId.assertAfter fvarId `h_named newEq pf
        --let (fvarId, mvarId'') ← mvarId'.intro1 #[fvarId]
        replaceMainGoal [result.mvarId]
      | none => throwError "Hypothesis is not an equality"


lemma hello (x y z d: ZMod 17) :  (((((x.val * y.val) % 17 + z.val) % 17 + d.val) % 17) = 5) -> ((x * y+ z + d).val = 5)  := by
  intros h
  rewrite_val_in_goal
  rw [h_named]
  exact h
  --trivial

lemma hi (x y z d: ZMod 17):  (x * y + z + d).val = (((x.val * y.val) % 17 + z.val) % 17 + d.val) % 17 := by
  trivial




elab "dump_named_hyps" hname:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    let targetName := hname.getId
    let some decl := lctx.findFromUserName? targetName
      | throwError m!"Could not find a hypothesis named `{targetName}`"
    logInfo m!"📌 {decl.userName} : {decl.type}"


  --intros h
  --rewrite_val_in_hyp h



  -- Now h is rewritten to:
  -- (((ZMod.val x + ZMod.val y) % 17 + ZMod.val z) % 17 = 5)
open Lean Meta Elab Tactic

partial def applyZModValRecursively (mvarId : MVarId) : TacticM (List MVarId) := do
  -- Set the goal we're working on
  setGoals [mvarId]
  -- Get the current goal type
  let goalType ← getMainTarget
  logInfo m!" Goal: {← ppExpr goalType}"
  match goalType.eq? with
  | some (_, lhs, rhs) =>
    logInfo m!" LHS: {← ppExpr lhs}"
    match lhs.getAppFnArgs with
    | (``ZMod.val, #[_, sumExpr]) =>
      logInfo m!"Matched ZMod.val on: {← ppExpr sumExpr}"
      match sumExpr.getAppFnArgs with
      | (``HAdd.hAdd, args) => do
          logInfo m!"Matched HAdd. Applying ZMod.val_add..."
          let subgoals ← getMainGoal >>= fun g => g.apply (mkConst ``ZMod.val_add)
          logInfo m!"Applied ZMod.val_add, new subgoals: {subgoals.length}"
          return ← List.flatten <$> subgoals.mapM applyZModValRecursively
          -- for sg in subgoals do
          --   try
          --     applyZModValRecursively sg
          --   catch err =>
          --     logInfo m!" Skipping subgoal: {← ppExpr (← sg.getType)}"
          --     logInfo m!"   Reason: {err.toMessageData}"
          --     pure ()
      | (``HMul.hMul, args) => do
          logInfo m!"Matched HAdd. Applying ZMod.val_mul..."
          let subgoals ← getMainGoal >>= fun g => g.apply (mkConst ``ZMod.val_mul)
          logInfo m!"Applied ZMod.val_add, new subgoals: {subgoals.length}"
          return ← List.flatten <$> subgoals.mapM applyZModValRecursively
          -- for sg in subgoals do
          --   try
          --     applyZModValRecursively sg
          --   catch err =>
          --     logInfo m!" Skipping subgoal: {← ppExpr (← sg.getType)}"
          --     logInfo m!"   Reason: {err.toMessageData}"
          --     pure ()
       | (``HSub.hSub, args) => do
          logInfo m!"Matched HAdd. Applying ZMod.val_mul..."
          let subgoals ← getMainGoal >>= fun g => g.apply (mkConst ``ZMod.val_sub)
          logInfo m!"Applied ZMod.val_sub, new subgoals: {subgoals.length}"
          return ← List.flatten <$> subgoals.mapM applyZModValRecursively
          -- for sg in subgoals do
          --   try
          --     applyZModValRecursively sg
          --   catch err =>
          --     logInfo m!" Skipping subgoal: {← ppExpr (← sg.getType)}"
          --     logInfo m!"   Reason: {err.toMessageData}"
          --     pure ()
      | _ =>
        logInfo m!" Not an HAdd inside val: {← ppExpr sumExpr}"
        return [mvarId]
    | _ =>
      logInfo m!" LHS is not ZMod.val: {← ppExpr lhs}"
      return [mvarId]
  | none =>
    logInfo m!" Goal is not an equality"
    return [mvarId]





elab "val_add_rec" : tactic => do
    let mvarId ← getMainGoal
    let remaining ← applyZModValRecursively mvarId
    setGoals remaining



--- Tests

example (a b c d : ZMod 17) :
  (( a + b + c) * d).val = (((((a.val + b.val) % 17 + c.val) % 17 )* d.val) % 17) := by
  val_add_rec


example (x y z : ZMod 17) :
  ((1- y)*z).val = (((1 - y.val) % 17) * z.val %17):= by
  apply Eq.trans (ZMod.val_mul (1 - y) z)


example (y : ZMod 11) :
  (1- y).val = 1 - y.val:= by
  val_add_rec
