import Lean
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval

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
  evalTactic (← `(tactic| try apply Nat.le_refl))
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  evalTactic (← `(tactic| try apply Nat.le_refl))
  evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
  evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
  evalTactic (← `(tactic| try apply Nat.le_refl))
  evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
  evalTactic (←  `(tactic|try apply Nat.le_refl))
  evalTactic (←  `(tactic| try rfl))

/-- Determines if any expression contains a subtraction in its arguments, recursively.  Does not go
under the indexing part of a vector indexing expression. -/
partial def containsSub (e : Expr) :  MetaM Bool := do
  let e ← instantiateMVars e
  if not e.isApp then return false
  match e.getAppFnArgs with
  | (``HSub.hSub, _) => return true
  | (``getElem, #[_,_,_,_,_, vectorExpr, _, _]) => containsSub vectorExpr
  | (_, args) => args.anyM containsSub

/-- Recurses through the expression to find all free variables that appear in it, either as is, or
as part of some vector indexing operation. -/
partial def collectVarsAppAndConst (e : Expr) : MetaM NameSet := do
  let e ← instantiateMVars e
  let lctx ← getLCtx
  if e.isFVar then
    if let some decl := lctx.find? e.fvarId! then
      return {decl.userName}
  if e.isApp then
    let (fn, args) := e.getAppFnArgs
    match (fn, args) with
    | (``getElem, #[_,_,_,_,_, vectorExpr, indexExpr, _]) =>
      if vectorExpr.isFVar then
        if let some decl := lctx.find? vectorExpr.fvarId! then
          let idxPretty ← PrettyPrinter.ppExpr indexExpr
          return {Name.mkSimple s!"{decl.userName}[{idxPretty}]"}
    | _ =>
      return (← args.mapM collectVarsAppAndConst).foldl (· ++ ·) {}
  return {}

-- | Introduces a name in the local context, passing a term for it to the continuation, so that it
-- can be used in a syntax quotation.  Useful for testing functions working over open expressions
def withVector (n : Name) (cont : Term → TacticM a) : TacticM a := do
  withLocalDecl n .default (← elabTerm (← `(Vector (ZMod 8) 32)) none) $ fun e => do
    let t ← PrettyPrinter.delab e
    cont t

def testCollectVarsAppAndConst (test : TacticM NameSet) : MetaM Unit :=
  Term.TermElabM.run' do
    let ns ← test { elaborator := .anonymous } |>.run' { goals := [] }
    logInfo m!"{ns.toList}"

def test1 : TacticM NameSet := do
  withVector `x $ fun x => withVector `y $ fun y => withVector `z $ fun z => do
    let e ← elabTerm (← `($x[8].val + ($y[2] * $z[5]).val = 0)) none
    collectVarsAppAndConst e

#eval testCollectVarsAppAndConst test1

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
  let split_ifs ← `(split_ifs)
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
      let goals_old ← getGoals
      --logInfo m!"Goal List: {goals_old}"
      -- let g := goals_old[0]!
      -- setGoals [g]
      evalTactic (← `(tactic| intro hMux))
      --evalTactic (← `(tactic| try simp at hMux))
      evalTactic (← `(tactic| try simp [hMux]))
      evalTactic (← `(tactic| try rw [Nat.mux_if_then] at ⊢))
      let goals_old ← getGoals
     -- logInfo m!"Goal List2: {goals_old}"
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
      --logInfo m!"{goalType}"
      let mut applied := false
      -- first we try to apply hypothesis
      let e ← instantiateMVars goalType
      let (_fn, args) := e.getAppFnArgs
     --logInfo m!"fun: {_fn}"
      let mut lemmaMatch := none
      let result ← collectVarsAppAndConst goalType
      let resultList := result.toList
      if !applied && args.size > 3 then
        let g ← getMainGoal
        let goalType ← g.getType
       -- logInfo m!"Goal:{g}"
        let e ← instantiateMVars goalType
        let (fn, args) := e.getAppFnArgs
        let unfolded := ← withTransparency .reducible (whnf args[2]!)
        let fn3 := unfolded.getAppFn
        let isVar := fn3.isFVar
        -- First check if we are dealing with a mux
        match viewAsMux args[2]! with
        | some (x, lhs@(_ :: _), rhs@(_ :: _)) =>
          let a := mkAddNat lhs
          let b := mkAddNat rhs
          let finalExpr ← g.withContext (rebuild x a b)
         -- logInfo m!"factored mux: {finalExpr}"
          let prop <- mkEq args[2]! finalExpr
          let pr := ← mkFreshExprMVar prop
          -- let eqId := pr.mvarId!
          -- create a new factored hyphesis
          let gWithHyp ← g.assert `hMux prop pr
          updatedGoals := updatedGoals ++ [pr.mvarId!, gWithHyp]
          --logInfo m!"NEW GOALS: {pr.mvarId!}"
          --logInfo m!"NEW GOALS: {gWithHyp}"
          applied := true
          handled := true
          progress := true
          did_mux := true
        | _ => pure ()
        -- if not a mux but we have only two variables do a case by case reasoning
        -- this is necessary in case of variable dependencies
        -- Ex: x1 + x2 - x1*x2 --> Can't be negative but needs to be proven
        -- - First check that only 2 variables exist & a subtraction is involved
        -- then make sure all variables are bounded <= 1
        if !applied && result.size == 2 && (<- containsSub goalType) then
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
                        return decl :: acc
                      else
                      return acc
                | _ => return acc
              | _ => return acc
          -- if bound exists apply a case split tactic
          if bounds.length = 2 then
            setGoals [g]
            g.withContext do
               -- logInfo m!"Goal: {goalType}"
              -- let lctx ← g.withContext getLCtx
                let h1 := mkIdent  bounds[0]!.userName
                let h2 := mkIdent  bounds[1]!.userName
                try
                  evalTactic (← `(tactic| elim2_norm_num $h1 $h2))
                catch _ => pure ()
               -- logInfo m!"❌ elim2_norm_num failed {err.toMessageData}"
              if ← g.isAssigned then
                  -- let newType ← g.getType
                  -- let t ← Meta.inferType (mkMVar g)
                  --logInfo m!"➖ elim2 modified goal "
                  let remaining ← getUnsolvedGoals
                  if remaining.contains g then
                    logInfo m!"➖ elim2 modified goal {g}, but did not fully solve it"
                  else
                    updatedGoals := updatedGoals ++ [g]
                    applied := true
                    handled := true
                    progress := true
              -- catch err =>
              --   logInfo m!"❌ elim2_norm_num failed {err.toMessageData}"
          else
            pure ()
           -- logInfo m!"❌ Did not find two appropriate bounds to run elim2_norm_num for {resultList}"
        --try to apply Lean's range analysis lemmas
        lemmaMatch := none
        --logInfo m!"NAME {fn3}"
        if (not applied) then
          if (result.size >0) then
            -- if we have variables then we can apply < C --> <= m?
            lemmaMatch :=
              match fn with
              | ``LT.lt =>
                match fn3 with
                | Expr.const name _ =>
                  match name with
                  | ``ite => some ("if", rfl)
                  | _ => some ("Nat.lt_of_le_of_lt", lt)
                | _ => none
              | _ => none
          if lemmaMatch.isNone then
            lemmaMatch :=
              match fn with
              | ``LE.le =>
                match fn3 with
                | Expr.const name _ =>
                  match name with
                  | ``HSub.hSub => some ("Nat.lt_sub", sub)
                  | ``HAdd.hAdd => some ("Nat.add_le_add", add)
                  | ``HMul.hMul => some ("Nat.mul_le_mul", mul)
                  | ``OfNat.ofNat => some ("@OfNat.ofNat", rfl)
                  -- rfl is a place holder should be something else
                  | ``ite => some ("if", rfl)
                  | ``ZMod.val => some ("ZMod", rfl)
                  | _ => none
                | _ => if isVar then some ("ZMod", rfl) else none
              | _ => none
         -- logInfo m!"Break"
        match lemmaMatch with
        | some ("if", _stx) =>
          --logInfo m!"We have a match?"
          evalTactic (← `(tactic| split_ifs))
          let goals <- getGoals
          -- logInfo m!"Goal List3: {goals}"
          updatedGoals := goals
          handled := true
          progress := true
          applied := true
        | some ("ZMod", _stx) =>
          -- logInfo m!"We have a var... {<-g.getType}"
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
        | some (_name, stx) =>
          try
            let e ← elabTerm stx goalType
            let subgoals ← g.apply e
            --logInfo m!" We applied a lemma {_name}"
            updatedGoals := updatedGoals ++ subgoals
            handled := true
            progress := true
            applied := true
          catch _err =>
            --logInfo m!" What happened? "
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
              --logInfo m!"➖ norm_num modified goal {g}, but did not fully solve it"
              applied := true
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
            progress := false
        catch _err =>
          updatedGoals := updatedGoals ++ [g]
          handled := true
          applied := true
          progress := false
    setGoals updatedGoals



--(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59]))*(x[60]*x[61] + (1 - x[60])*(1 - x[61]))*(x[62]*x[63] + (1 - x[62])*(1 - x[63])))

-- example (x: Vector (ZMod 7) 32)  (h1: x[0].val <= 1) (h2: x[1].val <= 1) (h3: x[2].val <= 1) (h4: x[3].val <= 1) (h5: x[4].val <= 1) (h6: x[5].val <= 1) (h7: x[6].val <= 1) (h8: x[7].val <= 1) (h9: x[8].val <= 1) (h10: x[9].val <= 1): (x[0].val*x[1].val + (1 - x[0].val)*(1 - x[1].val))*(x[2].val*x[3].val + (1 - x[2].val)*(1 - x[3].val)) *(x[4].val*x[5].val + (1 - x[4].val)*(1 - x[5].val))* (x[6].val*x[7].val + (1 - x[6].val)*(1 - x[7].val))*(x[8].val*x[9].val + (1 - x[8].val)*(1 - x[9].val))  < 2 :=
-- by try_apply_lemma_hyps [h1, h2, h3, h4, h5, h6, h7 , h8, h9, h10]

example (y x a b: ℕ) (h: x<=1 ) (h2: y<=1) (h7: z<= 1) (h3: a<= 1) (h4: b<= 1):
      (1-x)  *(2*a + b) +
      x *  (3*a + b) +
      (1-x) * (4 *a + b) < 9 := by
      try_apply_lemma_hyps [h3, h4, h2,h7, h]
      -- simp
      -- apply h3
      -- simp
      -- apply h4
      -- apply Nat.mul_le_mul
       --+
      -- (1-x) * y * (1-z) *(4*a + b) +
