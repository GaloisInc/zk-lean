import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval

open Lean Meta Elab Tactic


lemma Nat.lt_sub (a :ℕ) (h: a <= 1) :
  (1 - a) <= 1 := by sorry

def ignoredConsts : NameSet :=
  #[``Nat, ``instLTNat, ``instLENat, ``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub].foldl
    (init := {}) fun s n => s.insert n

partial def collectVarsAppAndConst (e : Expr) (acc : NameSet := {}) : MetaM NameSet := do
  --logInfo m!"🔍 Visiting: {← ppExpr e}"
  let mut acc := acc

  let e ← instantiateMVars e
  if e.isFVar then
    let fvarId := e.fvarId!
    let lctx ← getLCtx
    if let some decl := lctx.find? fvarId then
      logInfo m!"✅ Found local var: {decl.userName}"
      acc := acc.insert decl.userName
    else
      logInfo m!"❌ Skipping local var"
      return acc
  if e.isApp then
    let args := e.getAppArgs
    for arg in args do
      acc ← collectVarsAppAndConst arg acc
    return acc
  else
    return acc

-- Main function: check if the 3rd argument has exactly two distinct names
def thirdExprHasTwoVarsAppAndConst (args : Expr) : MetaM Bool := do
  logInfo m!"Args: {args}"
  let vars ← collectVarsAppAndConst args
  return vars.size == 2


private def tryApplyLemma (g : MVarId) (goalType : Expr) (stx : TSyntax `term) (name : String) : TacticM Bool := do
  try
    let e ← elabTerm stx goalType
    let subgoals ← g.apply e
    logInfo m!"✅ Applied {name} to goal {← PrettyPrinter.ppExpr goalType}"
    setGoals subgoals
    return true
  catch err =>
    logInfo m!"❌ Failed to apply {name} to goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
    return false

partial def findConstHead? (e : Expr) : Option Name :=
  match e with
  | Expr.const name _ => some name
  | Expr.app f _ => findConstHead? f
  | Expr.mdata _ b => findConstHead? b
  | Expr.proj _ _ b => findConstHead? b
  | _ => none

syntax (name := tryApplyLemHyps) "try_apply_lemma_hyps" ppSpace "[" ident,* "]" : tactic

@[tactic tryApplyLemHyps]
elab_rules : tactic
| `(tactic| try_apply_lemma_hyps [$hs,*]) => do
  let hyps := (hs.getElems.map (·.getId)).toList
  let mut progress := true
  let lt ← `(Nat.lt_of_le_of_lt)
  let sub ← `(Nat.lt_sub)
  let add ← `(Nat.add_le_add)
  let mul ← `(Nat.mul_le_mul)
  let rfl ← `(Nat.le_refl)
  let lemmas : List (TSyntax `term × String) := [
    (← `(Nat.lt_of_le_of_lt), "Nat.lt_of_le_of_lt"),
    (← `(Nat.lt_sub), "Nat.lt_sub"),
    (← `(Nat.add_le_add), "Nat.add_le_add"),
    (← `(Nat.mul_le_mul), "Nat.mul_le_mul"),
  ]
  let mut first_lemma := true
  let mut random := false
  while progress do
    progress := false
    let goals ← getGoals
    let mut updatedGoals : List MVarId := []
    let mut handled := false
    for g in goals do
      -- goal was solved so we don't need to do it
      if ← g.isAssigned then
        updatedGoals := updatedGoals ++ [g]
        continue
      -- handled exists so we only do the first goal as opposed to iterating through them all
      if handled then
        updatedGoals := updatedGoals ++ [g]
        continue
       -- Focus on one goal at a time
      setGoals [g]
      let goalType ← g.getType
      --logInfo m!"🧪 Solving goal {g}"
      let mut applied := false
      for hName in hyps do
          unless applied do
          --logInfo m!"🧪 Trying hypothesis {hName}"
          try
        let subgoals ← g.withContext do
          let lctx ← getLCtx
          let some decl := lctx.findFromUserName? hName
            | throwError m!"❌ Could not find a hypothesis named `{hName}`"
          let hExpr := mkFVar decl.fvarId
          g.apply hExpr
        -- outside `withContext` block: safe to mutate
        updatedGoals := updatedGoals ++ subgoals
        applied := true
        handled := true
        progress := true
      catch err =>
        random := false
        --logInfo m!"❌ Failed to apply {hName}: {← err.toMessageData.toString}"
      let (fn, args) := goalType.getAppFnArgs
      if !applied && args.size > 3 then
        let g ← getMainGoal
        let goalType ← g.getType
        let (fn, args) := goalType.getAppFnArgs
        let unfolded := ← withTransparency .reducible (whnf args[2]!)
        let fn3 := unfolded.getAppFn
        logInfo m!"SOS: looking at {goalType}"
        let result ← thirdExprHasTwoVarsAppAndConst goalType
        logInfo m!"result: {result}"
        let mut lemmaMatch := none
        if (first_lemma) then
          first_lemma := false
          lemmaMatch :=
            match fn with
            | name =>
              match name with
              | ``LT.lt => some ("Nat.lt_of_le_of_lt", lt)
              | _ => none
        else
          lemmaMatch :=
            match fn with
            | name =>
              match name with
              | ``LE.le =>
                -- THIS SHOULD BE MATCH LATER
                match fn3 with
                | Expr.const name _ =>
                  match name with
                    --| ``LT.lt => some ("Nat.lt_of_le_of_lt", lt)
                    | ``HSub.hSub => some ("Nat.lt_sub", sub)
                    | ``HAdd.hAdd => some ("Nat.add_le_add", add)
                    | ``HMul.hMul => some ("Nat.mul_le_mul", mul)
                    | ``OfNat.ofNat => some ("@OfNat.ofNat", rfl)
                    | _ => none
                | _ => none
              | _ => none
        match lemmaMatch with
        | some (name, stx) =>
            try
              --logInfo m!"Looking at lemma {name}"
              let e ← elabTerm stx goalType
              let subgoals ← g.apply e
              --logInfo m!"✅ Applied lemma {name} to goal {← PrettyPrinter.ppExpr goalType}"
              updatedGoals := updatedGoals ++ subgoals
              handled := true
              progress := true
              applied := true
            catch err =>
              random := false
              --logInfo m!"❌ Failed to apply lemma {name} to goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
        | none =>
            random := false
            --logInfo m!"❌ Failed to find a lemma for {fn} and args {args}"
      if not applied then
        try
          evalTactic (← `(tactic| norm_num))
          if ← g.isAssigned then
            let newType ← g.getType
            let t ← Meta.inferType (mkMVar g)
    -- you can also choose to restore the goal or stop here
            let remaining ← getUnsolvedGoals
            if remaining.contains g then
              logInfo m!"➖ norm_num modified goal {g}, but did not fully solve it"
            else
              logInfo m!"✅ Fully solved goal {g} using norm_num"
              updatedGoals := updatedGoals ++ [g]
              applied := true
              handled := true
          else
            logInfo m!"❌ did not solve the goal? {g}"
            updatedGoals := updatedGoals ++ [g]
            applied := true
            handled := true
        catch err =>
          logInfo m!"❌ norm_num failed on goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
          updatedGoals := updatedGoals ++ [g]
          handled := true
          applied := true
    setGoals updatedGoals





-- example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) * y < 17 := by
--   try_apply_lemma_hyps [h1,h2]




-- example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) + (1 - y) * x < 17 := by
--    try_apply_lemma_hyps [h1,h2]




-- example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) * (1 - y) * x < 17 := by
--   try_apply_lemma_hyps [h1,h2]


-- example (x y : ℕ):  (h1 : x ≤ 1) -> (h2 : y ≤ 1) -> 2 * (1 - y) + 4 * (1-x) < 17 := by
--   intros h1
--   intros h2
--   try_apply_lemma_hyps [h1,h2]


-- We need a way of catching when norm_num returns false
--


elab "prove_lt_by_cases" : tactic => do
  -- Step 2: insert `Nat.le_refl 1` `
  evalTactic (← `(tactic| apply Nat.le_trans _ (by exact Nat.le_refl 1)))
  -- Step 3: case split on x and y
  -- evalTactic (← `(tactic|
  --   cases x with
  --   | zero =>
  --     cases y with
  --     | zero => norm_num
  --     | succ y' =>
  --       cases y' with
  --       | zero => norm_num
  --       | succ _ => contradiction
  --   | succ x' =>
  --     cases x' with
  --     | zero =>
  --       cases y with
  --       | zero => norm_num
  --       | succ y' =>
  --         cases y' with
  --         | zero => norm_num
  --         | succ _ => contradiction
  --     | succ _ => contradiction
  -- ))

example (x y : ℕ): (h1 : x ≤ 1) → (h2 : y ≤ 1) →  (x * (1 - y) + y * (1 - x)) < 17 := by
  intros h1 h2
  apply Nat.lt_of_le_of_lt
  prove_lt_by_cases



example (x y : ℕ) (hx : x ≤ 1) (hy : y ≤ 1) :
    2 * (x * (1 - y) + y * (1 - x)) < _ := by
  apply Nat.lt_of_lt_of_le _ (by norm_num)
