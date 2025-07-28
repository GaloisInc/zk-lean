import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Lean Meta Elab Tactic

elab "apply_until_stuck" : tactic => do
  let mut goals ← getGoals

  -- Convert user-provided `ident`s to `Expr × String` pairs
  -- let locals ← hs.mapM fun id => do
  --   let fvarId ← getFVarId id
  --   pure (mkFVar fvarId, id.getId.toString)

  -- Hardcoded lemma names as syntax
  let hardcodedLemmas : List (TSyntax `term × String) := [
    (← `(Eq.symm), "Eq.symm"),
    (← `(Nat.le_trans), "Nat.le_trans"),
    (← `(Nat.lt_of_lt_of_le), "Nat.lt_of_lt_of_le")
    -- Add more as needed
  ]

  -- Elaborate them like `apply?` would
  let globs ← hardcodedLemmas.mapM fun (stx, name) => do
    let e ← elabTerm stx none
    pure (e, name)

  let allExprs := globs

  let mut progress := true
  while progress do
    progress := false
    let mut newGoals : List MVarId := []
    for g in goals do
      let mut goalSolved := false
      for (e, name) in allExprs do
        try
          logInfo m!"Trying to apply {name}..."
          let gs ← g.apply e
          logInfo m!"✅ Success applying {name}, produced {gs.length} subgoals"
          newGoals := newGoals ++ gs
          progress := true
          goalSolved := true
          break
        catch err =>
          logInfo m!"❌ Failed to apply {name}: {← err.toMessageData.toString}"
      if ¬goalSolved then
        newGoals := newGoals ++ [g]
    goals := newGoals
    logInfo m!"End of round: {goals.length} goals remaining"

  setGoals goals


example (h : x = y) : y = x := by
  --apply_until_stuck
  apply Eq.symm
  trivial


elab "try_apply_lemmas" : tactic => do
  let g ← getMainGoal
  let goalType ← g.getType

  let lemmas : List (TSyntax `term × String) := [
    (← `(Eq.symm), "Eq.symm"),
    (← `(Nat.lt_of_lt_of_le), "Nat.lt_of_lt_of_le"),
    (← `(Nat.lt_sub), "Nat.lt_sub"),
    (← `(Nat.mul_le_mul), "Nat.mul_le_mul")
  ]

  let mut succeeded := false
  let mut newGoals := [g]

  for (stx, name) in lemmas do
    if succeeded then break
    try
      let e ← elabTerm stx goalType
      let subgoals ← g.apply e
      logInfo m!"✅ Successfully applied {name}"
      newGoals := subgoals
      succeeded := true
    catch err =>
      logInfo m!"❌ Failed to apply {name}: {← err.toMessageData.toString}"

  setGoals newGoals


example (h : x = y) : y = x := by
  try_apply_lemmas
  --apply_until_stuck
  trivial

example (x y : ℕ) (h1 : x ≤ 1) (h2 : y ≤ 1) : (1-x) * y < 17 := by
  try_apply_lemmas
  --apply Nat.lt_of_le_of_lt




elab "apply_until_stuck2" hs:ident* : tactic => do
  let mut goals ← getGoals

  -- Turn local hypothesis identifiers into Expr × String pairs
  let locals ← hs.mapM fun id => do
    let fvarId ← getFVarId id
    pure (mkFVar fvarId, id.getId.toString)

  -- Hardcoded global lemmas, as quoted syntax
  let hardcodedLemmas : List (TSyntax `term × String) := [
    (← `(Eq.symm), "Eq.symm"),
    (← `(Nat.le_trans), "Nat.le_trans"),
    (← `(Nat.lt_of_lt_of_le), "Nat.lt_of_lt_of_le"),
    (← `(Nat.lt_of_le_of_lt), "Nat.lt_of_le_of_lt"),
    (← `(Nat.lt_trans), "Nat.lt_trans")
  ]

  -- Elaborate them in goal context like apply? would
  let globs ← hardcodedLemmas.mapM fun (stx, name) => do
    pure (stx, name)

  let allExprs := locals ++ globs

  let mut round := 0
  let mut progress := true
  while progress do
    round := round + 1
    logInfo m!"\n--- Round {round} ---"
    progress := false
    let mut newGoals : List MVarId := []
    for g in goals do
      let mut goalSolved := false
      let goalType ← g.getType
      for (eRaw, name) in allExprs do
        try
          let e ← match eRaw with
            | (e : Expr, name) => pure e
            | (stx, name) => elabTerm stx goalType
          logInfo m!"Trying to apply {name}..."
          let subgoals ← g.apply e
          logInfo m!"✅ Success applying {name}, produced {subgoals.length} subgoals"
          newGoals := newGoals ++ subgoals
          progress := true
          goalSolved := true
          break
        catch err =>
          logInfo m!"❌ Failed to apply {name}: {← err.toMessageData.toString}"
      if ¬goalSolved then
        newGoals := newGoals ++ [g]
    goals := newGoals
    logInfo m!"End of round {round}: {goals.length} goals remaining"

  setGoals goals
