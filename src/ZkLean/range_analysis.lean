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



lemma Nat.mux_if_then {a y x : ℕ} (h: a <= 1) :
  (1 - a) * x  + (a * y) = if a == 0 then x else y := by
  apply split_one at h
  apply Or.elim h
  simp
  intros h1
  rw [h1]
  simp
  intros h1
  rw [h1]
  simp


def mkAddNat (es : List Expr) : Expr :=
  match es with
  | []      => mkNatLit 0
  | [e]     => e
  | e :: es => mkApp2 (mkConst ``Nat.add) e (mkAddNat es)

-- rebeuilding a mux expression factored
def rebuild (x sumA sumB : Expr) : MetaM Expr := do
  let one       := mkNatLit 1
  let oneMinusX := mkApp2 (mkConst ``Nat.sub) one x
  let term1     := mkApp2 (mkConst ``Nat.mul) x sumA
  let term2     := mkApp2 (mkConst ``Nat.mul) oneMinusX sumB
  let res       := mkApp2 (mkConst ``Nat.add) term2 term1
  return res

-- Inspects the expression to possibly extract mux elements.
-- Ex: xA + (1-x)B + xC --> some (x, [A,C], [B])
partial def viewAsMux (e : Expr) : Option (Expr × List Expr × List Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, lhs, rhs])  => do
    let (lv, las, lbs) ← viewAsMux lhs
    let (rv, ras, rbs) ← viewAsMux rhs
    if (lv != rv) then none
    (lv, las ++ ras, lbs ++ rbs)
  | (``HMul.hMul, #[_, _, _, _, lhs, rhs]) =>
    match lhs.getAppFnArgs with
    | (``HSub.hSub, #[_, _, _, _, _, subRHS]) => some (subRHS, [], [rhs])
    | _ => some (lhs, [rhs], [])
  | _ => none

-- does split by cases reasoning
elab "elim2_norm_num" h1:ident h2:ident : tactic => do
  let id1 : TSyntax `ident := mkIdent h1.getId
  let id2 : TSyntax `ident := mkIdent h2.getId
  evalTactic (← `(tactic| apply split_one at $(id1):ident))
  evalTactic (← `(tactic| apply split_one at $(id2):ident))
  evalTactic (← `(tactic| apply Or.elim $id1))
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  evalTactic (←  `(tactic| try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic|try rfl))
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))


-- determines if an expression contains a subtraction
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

--
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


-- Main Range Analtsis Tactic
-- Args: list of hypothesis
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
  let mut random := false
  -- begin by factoring out multiplication for all goals
  -- important for mux discovery
  evalTactic (← `(tactic| try all_goals simp [Nat.mul_assoc]))
  let mut did_mux := false
  let mut did_decide:= false
  -- as long as we are making progress then continue
  while progress do
    if did_mux then
      -- for muxes we need to prove the factored lemma and split by
      -- cases
      evalTactic (← `(tactic| try simp))
      evalTactic (← `(tactic| try ring))
    if did_mux then
      evalTactic (← `(tactic| intro hMux))
      evalTactic (← `(tactic| rw [hMux]))
      evalTactic (← `(tactic| try simp))
      evalTactic (← `(tactic| try rw [Nat.mux_if_then]))
      evalTactic (← `(tactic| try split_ifs))
      did_mux := false
      progress := true
    let goals ← getGoals
    --  keep track of goals we changed
    let mut updatedGoals : List MVarId := []
    let mut handled := false
    progress := false
    for g in goals do
      -- if goal is asigned it is solved and should not be manipulated after
      if ← g.isAssigned then
        updatedGoals := updatedGoals ++ [g]
        continue
      -- we always want to only do the first goal that applies and then start from
      -- top of the queue
      if handled then
        updatedGoals := updatedGoals ++ [g]
        continue
       -- Focus on one goal at a time
      setGoals [g]
      let goalType ← g.getType
      let mut applied := false
      -- first we try to apply hypothesis
      for hName in hyps do
          unless applied do
          try
          -- need to do it with context so names are initialized
        let subgoals ← g.withContext do
          let lctx ← getLCtx
          let some decl := lctx.findFromUserName? hName
            | throwError m!"❌ Could not find a hypothesis named `{hName}`"
          let hExpr := mkFVar decl.fvarId
          g.apply hExpr
        updatedGoals := updatedGoals ++ subgoals
        applied := true
        handled := true
        progress := true
      catch _err =>
        random := false
      let e ← instantiateMVars goalType
      let (_fn, args) := e.getAppFnArgs
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
        match viewAsMux args[2]! with
        | some (x, lhs@(_ :: _), rhs@(_ :: _)) =>
          let a := mkAddNat lhs
          let b := mkAddNat rhs
          let finalExpr ← g.withContext (rebuild x a b)
          let prop <- mkEq args[2]! finalExpr
          let pr := ← mkFreshExprMVar prop
          -- let eqId := pr.mvarId!
          -- create a new factored hyphesis
          let gWithHyp ← g.assert `hMux prop pr
          replaceMainGoal [pr.mvarId!, gWithHyp]
          updatedGoals := updatedGoals ++ [pr.mvarId!, gWithHyp]
          setGoals updatedGoals
          applied := true
          handled := true
          progress := true
          did_mux := true
        | _ =>
          -- if not a mux but we have only two variables do a case by case reasoning
          -- this is necessary in case of variable dependencies
          -- Ex: x1 + x2 - x1*x2 --> Can't be negative but needs to be proven
          --- First check that only 2 variables exist & a subtraction is involved
          -- then make sure all variables are bounded <= 1
          if result.size == 2 && (<- containsSub goalType) then
            let bounds ← g.withContext do
              let lctx ← getLCtx
              hyps.foldlM (init := []) fun acc hName => do
                let some decl := lctx.findFromUserName? hName
                  | throwError m!"❌ Could not find a hypothesis named `{hName}`"
                match decl.type.getAppFnArgs with
                | (``LE.le, #[_, _, lhs, rhs]) =>
                  match (← whnf rhs) with
                  | (Expr.lit (Literal.natVal 1)) => do
                    let LHSvars ← collectVarsAppAndConst lhs
                    let varsList := LHSvars.toList
                    if LHSvars.size == 1 && resultList.contains varsList[0]! then
                          return decl.userName :: acc
                        else
                        return acc
                  | _ => return acc
                | _ => return acc
            -- if bound exists apply a case split tactic
            if bounds.length = 2 then
              -- let lctx ← g.withContext getLCtx
              let h1 := mkIdent  bounds[0]!
              let h2 := mkIdent bounds[1]!
              try
                evalTactic (← `(tactic| elim2_norm_num $h1 $h2))
                if ← g.isAssigned then
                  -- let newType ← g.getType
                  -- let t ← Meta.inferType (mkMVar g)
                  let remaining ← getUnsolvedGoals
                  if remaining.contains g then
                    logInfo m!"➖ elim2 modified goal {g}, but did not fully solve it"
                  else
                    updatedGoals := updatedGoals ++ [g]
                    applied := true
                    handled := true
                    progress := true
              catch err => logInfo m!"❌ elim2_norm_num failed {err.toMessageData}"
          --else
            --logInfo m!"❌ Did not find two appropriate bounds to run elim2_norm_num for {resultList}"
        -- try to apply Lean's range analysis lemmas
        lemmaMatch := none
        if (not applied) then
          if (result.size >0) then
            -- if we have variables then we can apply < C --> <= m?
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
          | some (_name, stx) =>
              try
                let e ← elabTerm stx goalType
                let subgoals ← g.apply e
                updatedGoals := updatedGoals ++ subgoals
                handled := true
                progress := true
                applied := true
              catch _err =>
                random := false
          | none =>
              random := false
      -- if other tectniques did not work try decide
      if not applied then
        let mut h <- getGoals
        try
          evalTactic (← `(tactic| decide))
          if ← g.isAssigned then
            -- let newType ← g.getType
            -- let t ← Meta.inferType (mkMVar g)
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
            updatedGoals := updatedGoals ++ [g]
            applied := true
            handled := true
        catch _err =>
          updatedGoals := updatedGoals ++ [g]
          handled := true
          applied := true
    setGoals updatedGoals





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
       try_apply_lemma_hyps [h3, h4, h2,h7,h]
