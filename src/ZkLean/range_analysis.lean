import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval
import Lean.Elab.Tactic.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod

open Lean Meta Elab Tactic

lemma split_one (x : ℕ): (x <= 1) -> (x = 0 ∨ x = 1) := by
  intro hx
  cases x with
    | zero => trivial
    | succ n => cases n with
      | zero =>
        apply Or.inr
        decide
      | succ m => exfalso
                  simp at hx

lemma Nat.lt_sub (a :ℕ) (h: a <= 1) :
  (1 - a) <= 1 := by
   apply split_one at h
   apply Or.elim h
   simp
   simp


lemma mux_chain_max {xs ys : ℕ} {sel : ℕ} (h : sel ≤ 1) :
  (1 - sel) * xs + sel * ys ≤ max xs ys := by
  sorry

-- this does not work because of the nested structure ...??
lemma Nat.mux_max {a y x n1 n2 : ℕ} (h: a <= 1) (h1: x <= n1) (h2: y<= n2) :
  (1 - a) * x  + (a * y) <= (if n1 > n2 then n1 else n2) := by
  sorry

lemma Nat.mux_max_2 {a y x n1 n2 : ℕ} (h: a <= 1) (h1: x <= n1) (h2: y<= n2) :
  (1 - a) * x  + (a * y) < (if n1 > n2 then n1 else n2) := by
  sorry

lemma Nat.mux_if_then {a y x : ℕ} (h: a <= 1) :
  (1 - a) * x  + (a * y) = if a == 0 then x else y := by
  sorry





def mkAddNat (es : List Expr) : Expr :=
  match es with
  | []      => mkNatLit 0
  | [e]     => e
  | e :: es => mkApp2 (mkConst ``Nat.add) e (mkAddNat es)

def rebuild (x sumA sumB : Expr) : MetaM Expr := do
  let one       := mkNatLit 1
  let oneMinusX := mkApp2 (mkConst ``Nat.sub) one x
  let term1     := mkApp2 (mkConst ``Nat.mul) x sumA
  let term2     := mkApp2 (mkConst ``Nat.mul) oneMinusX sumB
  let res       := mkApp2 (mkConst ``Nat.add) term2 term1
  return res


partial def collectExprs (x : Expr) : MetaM (Expr × List Expr × List Expr) := do
  --let mut as : List Expr := []
  --let mut bs : List Expr := []

  let (fn, args) := x.getAppFnArgs
  if args.size < 3 then
    return (x, [], [])
  match fn with
    | ``HAdd.hAdd  =>
    let (v', as', bs') ← collectExprs args[args.size -1]!
    if as'.isEmpty && bs'.isEmpty then
        return (x, [],[])
    let mut (v, as,bs) ← collectExprs args[args.size -2]!
    if as.isEmpty && bs.isEmpty then
        return (x, [],[])
    if (v' != v) then
       return (x, [],[])
    return (v, as ++ as', bs++bs')
    | ``HMul.hMul =>
       -- logInfo m!"Mul case"
        let (fn2, args2) := args[args.size -2]!.getAppFnArgs
        -- if args2.size <3 then
        --   return (x, [], [])
        match fn2 with
          | ``HSub.hSub => return (args2[args2.size -1]!, [], [args[args.size -1]!])
          | _ => return (args[args.size -2]!, [args[args.size -1]!], [])
    | _ => return (x, [],[],)


def classify (x : Expr) : MetaM Expr := do
  -- gettting rid of the <=
  let (fn, args) := x.getAppFnArgs
  -- now recursively split of the addition
  let (v, hi, hello) <- collectExprs args[2]!
  let a := mkAddNat hi
  let b := mkAddNat hello
  let finalExpr ← rebuild v a b
  logInfo m!"{finalExpr}"
  --logInfo m!"ARGS {args2}"
  return finalExpr


syntax (name := factorMux) "factorMux " : tactic

elab_rules : tactic
| `(tactic| factorMux) => do
  try
    evalTactic (← `(tactic| simp [Nat.mul_assoc]))
  catch _ => pure ()
  withMainContext do
    let g ← getMainGoal
    let goalType ← g.getType
    let (fn, args) := goalType.getAppFnArgs
    let h <- classify goalType
    let prop ← mkEq args[2]! h
    let pr  ← mkFreshExprMVar prop
    let gWithHyp ← g.assert `h30 prop pr
    let (hvar,b)← gWithHyp.intro1P
    --let hUserName ← hvar.getUserName
    replaceMainGoal [pr.mvarId!, b]
    focus
      do
        evalTactic (← `(tactic| simp))
        try
          evalTactic (← `(tactic| ring))
        catch _ => pure ()
  withMainContext do
    let lctx ← getLCtx
    match lctx.findFromUserName? `h30 with
    | some decl =>
      -- Build an `ident` for the hypothesis from its FVarId
      let hid : TSyntax `ident := mkIdent decl.userName
      -- Now you can run `simp at h30`
      evalTactic (← `(tactic| rw [$(hid):ident]))
      try
        evalTactic (← `(tactic| simp ))
      catch _ => pure ()
      evalTactic (← `(tactic| rw [Nat.mux_if_then]))
      evalTactic (← `(tactic| split_ifs))
    | none =>
        throwError "hypothesis `h30` not found in this goal"



elab "elim2_norm_num" h1:ident h2:ident : tactic => do
  let id1 : TSyntax `ident := mkIdent h1.getId
  let id2 : TSyntax `ident := mkIdent h2.getId
  evalTactic (← `(tactic| apply split_one at $(id1):ident))
  evalTactic (← `(tactic| apply split_one at $(id2):ident))
  evalTactic (← `(tactic| apply Or.elim $id1))
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()

  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  try
      evalTactic (←  `(tactic|apply Nat.le_refl))
  catch _ => pure ()



partial def containsSub (e : Expr) :  MetaM Bool := do
  let e <- instantiateMVars e
  if e.isApp then
    let args := e.getAppArgs
    let f := e.getAppFn
    if f.isConstOf ``HSub.hSub then
      return true
    --   | _ => logInfo m!"Failed on args of const"
    match args with
    | #[_,_,_,_,_, arg1, arg2, _] =>
       if arg1.isFVar then
          return false
    | _ => for arg in args do
              if ← containsSub arg then
           return true
  return false


partial def collectVarsAppAndConst (e : Expr) (acc : NameSet := {}) : MetaM NameSet := do
  let mut acc := acc
  let old_e := e
  let e ← instantiateMVars e
  let f := e.getAppFn
  if e.isFVar then
    let fvarId := e.fvarId!
    let lctx ← getLCtx
    if let some decl := lctx.find? fvarId then
      acc := acc.insert decl.userName
    else
      return acc
  if e.isApp then
    let args := e.getAppArgs
    let f := e.getAppFn
    match args with
    | #[_,_,_,_,_, arg1, arg2, _] =>
       if arg1.isFVar then
          let fvarId := arg1.fvarId!
          let lctx ← getLCtx
          if let some decl := lctx.find? fvarId then
            let idxPretty ← PrettyPrinter.ppExpr arg2
            let idxStr := s!"{idxPretty}"
            acc:= acc.insert (Name.mkSimple s!"{decl.userName}[{idxStr}]")
            return acc
    | _ => for arg in args do
              acc ← collectVarsAppAndConst arg acc
          return acc
  else
    return acc



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
  try
       evalTactic (← `(tactic| all_goals simp [Nat.mul_assoc]))
   catch _ => pure ()
  let mut did_mux := false
  let mut did_decide:= false
  while progress do
    if did_mux then
      try
        evalTactic (← `(tactic| simp))
      catch _ => logInfo m!"did not need simp?"
      try
        evalTactic (← `(tactic| ring))
      catch _ => logInfo m!"did not need ring?"
    if did_mux then
       evalTactic (← `(tactic| intro hMux))

       evalTactic (← `(tactic| rw [hMux]))
       try
         evalTactic (← `(tactic| simp ))
        catch _ => pure ()
       try
          evalTactic (← `(tactic| rw [Nat.mux_if_then]))
       catch _ => pure ()
       try
          evalTactic (← `(tactic| split_ifs))
       catch _ => pure ()
       did_mux := false
       progress := true
    let goals ← getGoals
    --   first_lemma := true
    let mut updatedGoals : List MVarId := []
    let mut handled := false
    progress := false
    for g in goals do
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
      logInfo m!"🧪 Solving goal {goalType}"
      let mut applied := false
      for hName in hyps do
          unless applied do
          try
        let subgoals ← g.withContext do
          let lctx ← getLCtx
          let some decl := lctx.findFromUserName? hName
            | throwError m!"❌ Could not find a hypothesis named `{hName}`"
          let hExpr := mkFVar decl.fvarId
          g.apply hExpr
        updatedGoals := updatedGoals ++ subgoals
        logInfo m!"We applied {hName}"
        applied := true
        handled := true
        progress := true
      catch err =>
        random := false
      let e ← instantiateMVars goalType
      let (fn, args) := e.getAppFnArgs
      --let e ← instantiateMVars goalType
      let mut lemmaMatch := none
      let result ← collectVarsAppAndConst goalType
      let resultList := result.toList
      if !applied && args.size > 3 then
        let g ← getMainGoal
        let goalType ← g.getType
         let e ← instantiateMVars goalType
        let (fn, args) := e.getAppFnArgs
        let unfolded := ← withTransparency .reducible (whnf args[2]!)
        let fn3 := unfolded.getAppFn
        -- First check if we are dealing with a mux
        -- now recursively split of the addition

        let (x, lhs, rhs) <- collectExprs args[2]!
        logInfo m!"We are here!! {lhs}, {rhs}"
        if (!lhs.isEmpty && !rhs.isEmpty) then
          --logInfo m!"We entered the desired loop with {g}"
          let a := mkAddNat lhs
          let b := mkAddNat rhs
          let finalExpr ← g.withContext (rebuild x a b)
          let prop <- mkEq args[2]! finalExpr
          let pr := ← mkFreshExprMVar prop
          let eqId := pr.mvarId!

          --let gWithHyp ← g.assert `hMux prop pr   -- adds h30 : lhs = finalExpr
          let gWithHyp ← g.assert `hMux prop pr
          replaceMainGoal [pr.mvarId!, gWithHyp]
          updatedGoals := updatedGoals ++ [pr.mvarId!, gWithHyp]
          --  let saved_l ← getGoals
          -- setGoals [eqId]
          -- try
          --   evalTactic (← `(tactic| simp))
          -- catch _ => logInfo m!"did not need simp?"
          -- try
          --   evalTactic (← `(tactic| ring))
          -- catch _ => logInfo m!"did not need ring?"
          -- let g_a <- getGoals
          -- updatedGoals := updatedGoals ++ g_a
          --updatedGoals := updatedGoals
          setGoals updatedGoals
          applied := true
          handled := true
          progress := true
          did_mux := true
        else
          if result.size == 2 && (<- containsSub goalType) then
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
                  -- logInfo m!"✅ Fully solved goal {goalType} using elim2"
                    updatedGoals := updatedGoals ++ [g]
                    applied := true
                    handled := true
                    progress := true
              catch err => logInfo m!"❌ elim2_norm_num failed {err.toMessageData}"
          --else
            --logInfo m!"❌ Did not find two appropriate bounds to run elim2_norm_num for {resultList}"
        let mut matched := true
        lemmaMatch := none
        if (not applied) then
          if (result.size >0) then
            --first_lemma := false
            lemmaMatch :=
              match fn with
              | name =>
                match name with
                | ``LT.lt => some ("Nat.lt_of_le_of_lt", lt)
                | _ => none
          if lemmaMatch.isNone then
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
         -- logInfo m!"Break"
          match lemmaMatch with

          | some (name, stx) =>
              try
                let e ← elabTerm stx goalType
                let subgoals ← g.apply e
               -- logInfo m!"✅ Applied lemma {name} to goal {← PrettyPrinter.ppExpr goalType}"
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
        --logInfo m!"We are here?"
        let mut h <- getGoals
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
              if h.length != 0 then
                progress := true
                did_decide := true
              else
                progress := false
          else
            --logInfo m!"❌ did not solve the goal? {g}"
            updatedGoals := updatedGoals ++ [g]
            applied := true
            handled := true
            -- if h.length != 0 then
            --   progress := true
            -- else
            --     progress := false
        catch err =>
          --logInfo m!"❌ decide failed on goal {← PrettyPrinter.ppExpr goalType}: {← err.toMessageData.toString}"
          updatedGoals := updatedGoals ++ [g]
          handled := true
          applied := true
          -- if h.length != 0 then
          --   progress := true
          -- else
          --       progress := false
      if (!progress) then
        logInfo m! "Why did I make no progress? {g}"
    setGoals updatedGoals

-- example (x y : ℕ): (h1 : (x <= 1) ) → (h1 : (y <= 1) ) → ( (z <= 1) ) -> ( (x * (1 - y) + y * (1 - x)) + (z * (1 - y) + y * (1 - z))) < 3 := by
--   intros h1 h2 h3
--   try_apply_lemma_hyps [h1, h2, h3]



-- so theorteically I would have 32 chunks so this needs to be a recursive lemma...



partial def collectExprs2 (x : Expr) : MetaM (Expr × List Expr × List Expr) := do
  --let mut as : List Expr := []
  --let mut bs : List Expr := []

  let (fn, args) := x.getAppFnArgs
  if args.size < 3 then
    return (x, [], [])
  match fn with
    | ``HAdd.hAdd  =>
    let (v', as', bs') ← collectExprs args[args.size -1]!
    if as'.isEmpty && bs'.isEmpty then
        return (x, [],[])
    let mut (v, as,bs) ← collectExprs args[args.size -2]!
    if as.isEmpty && bs.isEmpty then
        return (x, [],[])
    if (v' != v) then
       logInfo m!"This is the issue..{v'}, {v}"
       return (x, [],[])
    return (v, as ++ as', bs++bs')
    | ``HMul.hMul =>
       -- logInfo m!"Mul case"
        let (fn2, args2) := args[args.size -2]!.getAppFnArgs
        -- if args2.size <3 then
        --   return (x, [], [])
        logInfo m!"ARGS {fn}"
        match fn2 with
          | ``HSub.hSub => return (args2[args2.size -1]!, [], [args[args.size -1]!])
          | _ => return (args[args.size -2]!, [args[args.size -1]!], [])
    | _ => return (x, [],[],)

syntax (name := Debug) "Debug" : tactic

elab_rules : tactic
| `(tactic| Debug) => do
    try
      evalTactic (← `(tactic| simp [Nat.mul_assoc]))
    catch _ => pure ()
     withMainContext do
      let g ← getMainGoal
      let goalType ← g.getType
      let (fn, args) := goalType.getAppFnArgs
      let h <- collectExprs2 args[2]!
      logInfo m!"{h}"


example (y x a b: ℕ) (h: x<=1 ) (h2: y<=1) (h7: z<= 1) (h3: a<= 1) (h4: b<= 1):
      (1-x) * (1-y)* (1-z) *(2*a + b) +
      x * (1-y) *(1-z) * (3*a + b) +
      (1-x) * y * (1-z) *(4*a + b) +
      x * y * (1-z) * (5*a + b) +
      (1-x) * (1-y)* z *(6*a + b) +
      x * (1-y) *z * (7*a + b) +
      (1-x) * y * z *(8*a + b) +
      x * y * z* (9*a + b)
       < 11  /\  (1-x) * (1-y)* (1-z) *(2*a + b) +
      x * (1-y) *(1-z) * (3*a + b) +
      (1-x) * y * (1-z) *(4*a + b) +
      x * y * (1-z) * (5*a + b) +
      (1-x) * (1-y)* z *(6*a + b) +
      x * (1-y) *z * (7*a + b) +
      (1-x) * y * z *(8*a + b) +
      x * y * z* (9*a + b)
       < 12 := by
       split_ands
       --all_goals simp [Nat.mul_assoc]
       try_apply_lemma_hyps [h3, h4, h2,h7,h]






    --   evalTactic (← `(tactic| rw [hMux]))
    --   evalTactic (← `(tactic| simp ))
    --   evalTactic (← `(tactic| rw [Nat.mux_if_then]))
    --   evalTactic (← `(tactic| split_ifs))






       --sorry






-- RQ :






       --try_apply_lemma_hyps [h3, h4, h2,h7,h]
      -- try_apply_lemma_hyps [h3, h4, h2,h7,h]
