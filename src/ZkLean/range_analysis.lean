import Lean
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Monad.Cont
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval

open Lean Meta Elab Tactic



lemma Nat.mul_comm_ofNat (a n : Nat) :
   (OfNat.ofNat n) * a = a* (OfNat.ofNat n : Nat) := by
  rw [Nat.mul_comm ]

 lemma mul_comm_num_left (n t : ℕ) :
  (n : ℕ) * t = t * (n : ℕ) := by
  simpa using Nat.mul_comm (n : ℕ) t

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
  if not e.isApp then return false
  match e.getAppFnArgs with
  | (``HSub.hSub, _) => return true
  | (``getElem, #[_,_,_,_,_, vectorExpr, _, _]) => containsSub vectorExpr
  | (_, args) => args.anyM containsSub

/-- Recurses through the expression to find all free variables that appear in it, either as is, or
as part of some vector indexing operation. -/
partial def collectTerms (e : Expr) : MetaM NameSet := do
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
      return (← args.mapM collectTerms).foldl (· ++ ·) {}
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
    collectTerms e

#eval testCollectVarsAppAndConst test1

-- Main Range Analysis Tactic
-- Args: list of hypothesis
syntax (name := tryApplyLemHyps) "try_apply_lemma_hyps" ppSpace "[" ident,* "]" : tactic

-- for muxes we need to prove the factored lemma and split by cases
def didMux : TacticM Unit := do
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try ring))
  evalTactic (← `(tactic| intro hMux))
  evalTactic (← `(tactic| try simp [hMux]))
  evalTactic (← `(tactic| try rw [Nat.mux_if_then] at ⊢))

structure LoopBodyResult where
  didMux : Bool
  madeProgress : Bool
  goals : List MVarId

def LoopBodyLabel := MonadCont.Label LoopBodyResult (ContT LoopBodyResult TacticM) Unit

def handleIfMux (loopBodyReturn : LoopBodyLabel) (g : MVarId) (args : Array Expr)
  : ContT LoopBodyResult TacticM Unit := do
  match viewAsMux args[2]! with
  | some (x, lhs@(_ :: _), rhs@(_ :: _)) =>
    let a := mkAddNat lhs
    let b := mkAddNat rhs
    let finalExpr ← monadLift $ g.withContext (rebuild x a b)
    let prop ← mkEq args[2]! finalExpr
    let pr ← mkFreshExprMVar prop
    -- create a new factored hyphesis
    let gWithHyp ← g.assert `hMux prop pr
    loopBodyReturn.apply { didMux := true, madeProgress := true, goals := [pr.mvarId!, gWithHyp] }
  | _ => return ()

def caseByCaseOnTwoVariables (loopBodyReturn : LoopBodyLabel)
  (g : MVarId) (hyps : List Name) (terms : NameSet)
  : ContT LoopBodyResult TacticM Unit := do
  let bounds ← monadLift $ g.withContext do
    let lctx ← getLCtx
    hyps.foldlM (init := []) fun acc hName => do
      let some decl := lctx.findFromUserName? hName
        | throwError m!"❌ Could not find a hypothesis named `{hName}`"
      match decl.type.getAppFnArgs with
      | (``LE.le, #[_, _, lhs, rhs]) =>
        match (← whnf rhs) with
        | (Expr.lit (Literal.natVal 1)) => do
          let LHSvars ← collectTerms lhs
          let varsList := LHSvars.toList
          if LHSvars.size == 1 && terms.contains varsList[0]! then
            return decl :: acc
          else
            return acc
        | _ => return acc
      | _ => return acc
  -- if bound exists apply a case split tactic
  if bounds.length = 2 then
    setGoals [g]
    monadLift $ g.withContext do
      let h1 := mkIdent  bounds[0]!.userName
      let h2 := mkIdent  bounds[1]!.userName
      evalTactic (← `(tactic| try elim2_norm_num $h1 $h2))
    if ← g.isAssigned then
      if (← getUnsolvedGoals).contains g then
        logInfo m!"➖ elim2 modified goal {g}, but did not fully solve it"
      else
        loopBodyReturn.apply { didMux := false, madeProgress := true, goals := [g] }

def applyIfLemma (loopBodyReturn : LoopBodyLabel) : ContT LoopBodyResult TacticM Unit := do
  monadLift $ do evalTactic (← `(tactic| split_ifs))
  loopBodyReturn.apply { didMux := false, madeProgress := true, goals := (← getGoals) }

def applyZModLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  for hName in hyps do
    try
      -- need to do it with context so names are initialized
      let subgoals ← monadLift $ g.withContext do
        let lctx ← getLCtx
        let some decl := lctx.findFromUserName? hName
          | throwError m!"❌ Could not find a hypothesis named `{hName}`"
        g.apply (mkFVar decl.fvarId)
      -- Note: `return` below makes sure we end the loop after jumping to the
      -- continuation
      return (← loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals })
    catch _err => pure ()

def applyThisLemma (loopBodyReturn : LoopBodyLabel) (g : MVarId) (goalType : Expr) (stx : Syntax)
  : ContT LoopBodyResult TacticM Unit := do
  try
    let subgoals ← g.apply (← elabTerm stx goalType)
    loopBodyReturn.apply { didMux := false, madeProgress := true, goals := subgoals }
  catch _ => pure ()

def findAndApplyRangeAnalysisLemma (loopBodyReturn : LoopBodyLabel)
  (terms : NameSet) (g : MVarId) (mainGoalType : Expr) (hyps : List Name)
  : ContT LoopBodyResult TacticM Unit := do
  let applyThisLemma := applyThisLemma loopBodyReturn g mainGoalType
  let lt ← monadLift (m := TacticM) ``(Nat.lt_of_le_of_lt)
  let sub ← monadLift (m := TacticM) ``(Nat.lt_sub)
  let add ← monadLift (m := TacticM) ``(Nat.add_le_add)
  let mul ← monadLift (m := TacticM) ``(Nat.mul_le_mul)
  let rfl ← monadLift (m := TacticM) ``(Nat.le_refl)
  let (fn, args) := mainGoalType.getAppFnArgs
  let unfolded := ← monadLift $ withTransparency .reducible (whnf args[2]!)
  let fn3 := unfolded.getAppFn
  if (terms.size > 0) then
    -- if we have variables then we can apply < C --> <= m?
    match fn with
    | ``LT.lt =>
      match fn3 with
      | Expr.const name _ =>
        match name with
        | ``ite => applyIfLemma loopBodyReturn
        | _ => applyThisLemma lt
      | _ => pure ()
    | _ => pure ()
  match fn with
  | ``LE.le =>
    match fn3 with
    | Expr.const name _ =>
      match name with
      | ``HSub.hSub => applyThisLemma sub
      | ``HAdd.hAdd => applyThisLemma add
      | ``HMul.hMul => applyThisLemma mul
      | ``OfNat.ofNat => applyThisLemma rfl
      -- rfl is a place holder should be something else
      | ``ite => applyIfLemma loopBodyReturn
      | ``ZMod.val => applyZModLemma loopBodyReturn g hyps
      | _ => pure ()
    | _ =>
      if fn3.isFVar then applyZModLemma loopBodyReturn g hyps
  | _ => pure ()

@[tactic tryApplyLemHyps]
elab_rules : tactic
| `(tactic| try_apply_lemma_hyps [$hs,*]) => do
  let hyps := (hs.getElems.map (·.getId)).toList
  let mut progress := true
  -- begin by factoring out multiplication for all goals
  -- important for mux discovery
  evalTactic (← `(tactic| try all_goals simp [Nat.mul_assoc]))
  let mut cont := true
  while cont do
    try
      evalTactic (← `(tactic| all_goals rw [Nat.mul_comm_ofNat]))
    catch _ =>
      cont := false
  evalTactic (← `(tactic| try all_goals simp [Nat.mul_assoc]))
  let mut did_mux := false
  -- as long as we are making progress then continue
  while progress do
    if did_mux then do
      didMux
      did_mux := false
    let goals ← getGoals
    let mut updatedGoals : List MVarId := [] -- to keep track of goals we changed
    let mut handled := false
    progress := false
    for g in goals do
      -- 1. If goal is asigned it is solved and should not be manipulated after
      -- 2. We always want to only do the first goal that applies and then start
      -- from top of the queue
      if (← g.isAssigned) || handled then
        updatedGoals := updatedGoals ++ [g]
        continue
      setGoals [g] -- focus on one goal at a time
      let goalType ← g.getType
      -- first we try to apply hypothesis
      let instantiatedGoalType ← instantiateMVars goalType
      let (_fn, args) := instantiatedGoalType.getAppFnArgs
      let terms ← collectTerms instantiatedGoalType
      -- Note: Here we use a continuation to let our callees return by
      -- short-circuiting the rest of the computation.
      let loopResult ← (ContT.run · pure) $ MonadCont.callCC $ fun loopBodyReturn => do
        if args.size > 3 then
          let g ← getMainGoal
          let goalType ← g.getType
          let e ← instantiateMVars goalType
          let args := e.getAppArgs
          -- First check if we are dealing with a mux
          handleIfMux loopBodyReturn g args
          -- if not a mux but we have only two variables do a case by case reasoning
          -- this is necessary in case of variable dependencies
          -- Ex: x1 + x2 - x1*x2 --> Can't be negative but needs to be proven
          -- - First check that only 2 variables exist & a subtraction is involved
          -- then make sure all variables are bounded <= 1
          if terms.size == 2 && (← containsSub instantiatedGoalType) then
            caseByCaseOnTwoVariables loopBodyReturn g hyps terms
          --try to apply Lean's range analysis lemmas
          findAndApplyRangeAnalysisLemma loopBodyReturn terms g instantiatedGoalType hyps
        -- if other techniques did not work try decide
        try
          monadLift $ do evalTactic (← `(tactic| decide))
          if ← g.isAssigned then
            logInfo m!"✅ Fully solved goal using decide {goalType}"
            return { didMux := false, madeProgress := true, goals := [g] }
        catch _err => pure ()
        -- if we made it here, nothing worked
        return { didMux := false, madeProgress := false, goals := [g] }
      if loopResult.didMux then did_mux := true
      if loopResult.madeProgress then handled := true; progress := true
      updatedGoals := updatedGoals ++ loopResult.goals
    setGoals updatedGoals


--(x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59]))*(x[60]*x[61] + (1 - x[60])*(1 - x[61]))*(x[62]*x[63] + (1 - x[62])*(1 - x[63])))

-- example (x: Vector (ZMod 7) 32)  (h1: x[0].val <= 1) (h2: x[1].val <= 1) (h3: x[2].val <= 1) (h4: x[3].val <= 1) (h5: x[4].val <= 1) (h6: x[5].val <= 1) (h7: x[6].val <= 1) (h8: x[7].val <= 1) (h9: x[8].val <= 1) (h10: x[9].val <= 1): (x[0].val*x[1].val + (1 - x[0].val)*(1 - x[1].val))*(x[2].val*x[3].val + (1 - x[2].val)*(1 - x[3].val)) *(x[4].val*x[5].val + (1 - x[4].val)*(1 - x[5].val))* (x[6].val*x[7].val + (1 - x[6].val)*(1 - x[7].val))*(x[8].val*x[9].val + (1 - x[8].val)*(1 - x[9].val))  < 2 :=
-- by try_apply_lemma_hyps [h1, h2, h3, h4, h5, h6, h7 , h8, h9, h10]

example (y x : ℕ) (h: x<=1 ) (h2: y<=1) (h3: z<=1):
     2 * ((x) * (1-y) * z) +
       8 * (x * (y) * (1-z)) +
      7* ((1-x) * y) * z +
      1 * (1-x)* (1-y) * (1-z)
       < 9 := by
      --  all_goals simp [Nat.mul_assoc]
      --  all_goals rw [Nat.mul_comm_ofNat]
      --  all_goals rw [Nat.mul_comm_ofNat]
      --  all_goals rw [Nat.mul_comm_ofNat]
       try_apply_lemma_hyps [ h2, h, h3]


--       -- simp
      -- apply h3
      -- simp
      -- apply h4
      -- apply Nat.mul_le_mul
       --+
      -- (1-x) * y * (1-z) *(4*a + b) +
