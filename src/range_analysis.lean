import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Lean Meta Elab Tactic


lemma Nat.lt_sub (a :ℕ) (h: a <= 1) :
  (1 - a) <= 1 := by sorry


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
      logInfo m!"🧪 Solving goal {g}"
      let mut applied := false
      for hName in hyps do
          unless applied do
          logInfo m!"🧪 Trying hypothesis {hName}"
          try
            let decl ← getLocalDeclFromUserName hName
            let hExpr := mkFVar decl.fvarId
            let subgoals ← g.apply hExpr
            logInfo m!"✅ Applied hypothesis {hName}"
            updatedGoals := updatedGoals ++ subgoals
            handled := true
            progress := true
            -- if we start hypothesis we should not be applying more lemmas
            applied := true
          catch err =>
            logInfo m!"❌ Failed to apply {hName} to goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
      let (fn, args) := goalType.getAppFnArgs
      if !applied && args.size > 3 then
        let g ← getMainGoal
        let goalType ← g.getType
        let (fn, args) := goalType.getAppFnArgs
        let unfolded := ← withTransparency .reducible (whnf args[2]!) -- ✅ still allowed here
        let fn3 := unfolded.getAppFn
        logInfo m!"SOS: looking at {args}"
        logInfo m!"SOS: looking at {fn3}"
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
              logInfo m!"Looking at lemma {name}"
              let e ← elabTerm stx goalType
              let subgoals ← g.apply e
              logInfo m!"✅ Applied lemma {name} to goal {← PrettyPrinter.ppExpr goalType}"
              updatedGoals := updatedGoals ++ subgoals
              handled := true
              progress := true
              applied := true
            catch err =>
              logInfo m!"❌ Failed to apply lemma {name} to goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
        | none =>
            logInfo m!"❌ Failed to find a lemma for {fn} and args {args}"
      if not applied then
        try
          evalTactic (← `(tactic| norm_num))
          if ← g.isAssigned then
            logInfo m!"✅ Solved goal {g} using norm_num"
            progress := true
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




example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) + (1 - y) * x < 17 := by
   try_apply_lemma_hyps [h1,h2]




example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) * (1 - y) * x < 17 := by
  try_apply_lemma_hyps [h1,h2]


example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) :  2 * (1 - y) < 17 := by
  try_apply_lemma_hyps [h1,h2]

  --try_apply_lemma_hyps [h1,h2]
