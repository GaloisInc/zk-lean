import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Lean Meta Elab Tactic


lemma Nat.lt_sub (a :ℕ) (h: a <= 1) :
  (1 - a) <= 1 := by sorry


syntax (name := tryApplyLemHyps) "try_apply_lemma_hyps" ppSpace "[" ident,* "]" : tactic

@[tactic tryApplyLemHyps]
elab_rules : tactic
| `(tactic| try_apply_lemma_hyps [$hs,*]) => do
  let hyps := (hs.getElems.map (·.getId)).toList
  let mut progress := true
  let lemmas : List (TSyntax `term × String) := [
    (← `(Nat.lt_of_le_of_lt), "Nat.lt_of_le_of_lt"),
    (← `(Nat.lt_sub), "Nat.lt_sub"),
    (← `(Nat.add_le_add), "Nat.add_le_add"),
    (← `(Nat.mul_le_mul), "Nat.mul_le_mul"),
  ]
  let mut started_hyp := false
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
      setGoals [g]  -- Focus on one goal at a time
      let goalType ← g.getType
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
            started_hyp := true
            applied := true
          catch err =>
            logInfo m!"❌ Failed to apply {hName} to goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
      if not applied && not started_hyp  then
        for (stx, name) in lemmas do
          unless applied do
            try
              let e ← elabTerm stx goalType
              let subgoals ← g.apply e
              logInfo m!"✅ Successfully applied lemma {name}"
              updatedGoals := updatedGoals ++ subgoals
              progress := true
              applied := true
              handled := true
            catch err =>
              logInfo m!"❌ Failed to apply lemma {name} to goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
      if not applied then
          updatedGoals := updatedGoals ++ [g]  -- keep original goal if no lemma applied
          handled := true

    setGoals updatedGoals




example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) * y < 17 := by
  try_apply_lemma_hyps [h1,h2]
  norm_num



example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1 - x) + (1 - y) * x < 17 := by
  try_apply_lemma_hyps [h1,h2]
  -- RQ: Why did it get stuc here??
  apply Nat.mul_le_mul
  try_apply_lemma_hyps [h1,h2]
  norm_num


-- ToDos
-- unite apply lemmas and apply hyps
-- unite with valify
