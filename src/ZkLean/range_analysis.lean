import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval
import Lean.Elab.Tactic.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod

open Lean Meta Elab Tactic

lemma split_one (x : ℕ): (x <= 1) -> (x = 0 ∨ x = 1) := by
  sorry


elab "elim2_norm_num" h1:ident h2:ident : tactic => do
  let id1 : TSyntax `ident := mkIdent h1.getId
  let id2 : TSyntax `ident := mkIdent h2.getId
  --let loc ← `(tactic.location| $id1)
  --let loc ← `(tactic.location| $id1)
  evalTactic (← `(tactic| apply split_one at $(id1):ident))
  evalTactic (← `(tactic| apply split_one at $(id2):ident))
  evalTactic (← `(tactic| apply Or.elim $id1))

  -- Case: intro hx
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; norm_num;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()

  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; norm_num;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()

  -- Case: intro hx again
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; norm_num;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; norm_num;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()


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
      --ogInfo m!"✅ Found local var: {decl.userName}"
      acc := acc.insert decl.userName
    else
      --logInfo m!"❌ Skipping local var"
      return acc
  if e.isApp then
    let args := e.getAppArgs
    match args with
    | #[_,_,_,_,_, arg1, arg2, _] =>
       if arg1.isFVar then
          --logInfo m!"{e}"
          let fvarId := arg1.fvarId!
          let lctx ← getLCtx
          if let some decl := lctx.find? fvarId then
            let idxPretty ← PrettyPrinter.ppExpr arg2
            let idxStr := s!"{idxPretty}"
            acc:= acc.insert (Name.mkSimple s!"{decl.userName}[{idxStr}]")
            return acc

    | _ => pure ()
    --logInfo m!"✅ Apss: {args}"
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

open Lean Meta

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
       -- logInfo m!"looking at {goalType}"
        let result ← collectVarsAppAndConst goalType
        let resultList := result.toList
        --logInfo m!"result: {resultList}"
        let mut lemmaMatch := none
        if result.size == 2 then
          --logInfo m!"Searching for bounds :)"
          let bounds ← g.withContext do
            let lctx ← getLCtx
            hyps.foldlM (init := []) fun acc hName => do
              let some decl := lctx.findFromUserName? hName
                | throwError m!"❌ Could not find a hypothesis named `{hName}`"
              --logInfo m!"decl hypothesis: {decl.type.getAppFnArgs}"
              match decl.type.getAppFnArgs with
              | (``LE.le, #[_, _, lhs, rhs]) =>
                 --logInfo m!"are we at least getting here1.. "
                 -- TODO: Need to figure out a way to do a check if rhs is actually 1
                 -- have a function that always returns true for now
                        let LHSvars  ← collectVarsAppAndConst lhs
                        let varsList := LHSvars.toList
                        --logInfo m!"LHS: {varsList}"
                        if LHSvars.size == 1 && resultList.contains varsList[0]! then
                              --logInfo m!"var: {varsList}}  present"
                              return decl.userName :: acc
                            else
                             -- logInfo m!"var: {varsList}} not present"
                             return acc
                | _ => return acc
          --logInfo m!"bounds: {bounds}"
          if bounds.length = 2 then
            let lctx ← g.withContext getLCtx
            let h1 := mkIdent  bounds[0]!
            let h2 := mkIdent bounds[1]!
            --logInfo m!"🚀 Applying elim2_norm_num with {h1}, {h2} on {goalType}"
            try
              evalTactic (← `(tactic| elim2_norm_num $h1 $h2))
              if ← g.isAssigned then
                let newType ← g.getType
                let t ← Meta.inferType (mkMVar g)
                let remaining ← getUnsolvedGoals
                if remaining.contains g then
                  logInfo m!"➖ elim2 modified goal {g}, but did not fully solve it"
                else
                  --logInfo m!"✅ Fully solved goal {g} using elim2"
                  updatedGoals := updatedGoals ++ [g]
                  applied := true
                  handled := true
                  progress := true
            catch err => pure ()
              --logInfo m!"❌ elim2_norm_num failed: {← err.toMessageData.toString}"
          else
            logInfo m!"❌ Did not find two appropriate bounds to run elim2_norm_num for {resultList}"
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
                match fn3 with
                | Expr.const name _ =>
                  match name with
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
      -- TODO Need to figure out how
        try
          evalTactic (← `(tactic| decide))
          if ← g.isAssigned then
            let newType ← g.getType
            let t ← Meta.inferType (mkMVar g)
            --logInfo m!"Goal Type: {t}"
            --logInfo m!"Goal Type: {newType}"
            --- TODO: see if eval somehow works

    -- you can also choose to restore the goal or stop here
            let remaining ← getUnsolvedGoals
            if remaining.contains g then
              logInfo m!"➖ norm_num modified goal {g}, but did not fully solve it"
            else
              logInfo m!"✅ Fully solved goal using decide {goalType}"
              updatedGoals := updatedGoals ++ [g]
              applied := true
              handled := true
          else
            logInfo m!"❌ did not solve the goal? {g}"
            updatedGoals := updatedGoals ++ [g]
            applied := true
            handled := true
        catch err =>
          logInfo m!"❌ decide failed on goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
          updatedGoals := updatedGoals ++ [g]
          handled := true
          applied := true
    setGoals updatedGoals

open Lean.Parser.Tactic



  --elim2_norm_num h1 h2



example (x y : ℕ): (h1 : (x <= 1) ) → (h1 : (y <= 1) ) → ( (z <= 1) ) -> ( (x * (1 - y) + y * (1 - x)) + (z * (1 - y) + y * (1 - z))) < 3 := by
  intros h1 h2 h3
  try_apply_lemma_hyps [h1, h2, h3]


abbrev ff := 4139
abbrev f := ZMod ff
abbrev b := Nat.log2 ff


example (fv1 fv2: Vector f 8) :  (ZMod.val fv1[0]  <= 1) -> ( ZMod.val fv2[1] <= 1) -> ( ZMod.val fv2[0] <= 1) ->
  ((ZMod.val fv1[0])*(1- ZMod.val fv2[1]) + (ZMod.val fv2[1])*(1-ZMod.val fv1[0])) +
  ((ZMod.val fv1[0])*(1- ZMod.val fv2[0]) + (ZMod.val fv2[0])*(1-ZMod.val fv1[0])) < 7 := by
  intros h1 h2 h3
  try_apply_lemma_hyps [h1, h2, h3]

 example (x y : ℕ) : (x <= 4) -> (y <= 4)  ->  x* (x+y) < 100 := by
     intros h1 h2
     apply Nat.lt_of_le_of_lt
     apply Nat.mul_le_mul
     apply h1
     apply Nat.add_le_add
     apply h1
     apply h2
     decide
