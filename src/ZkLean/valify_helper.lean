import Lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Eval
import Lean.Elab.Tactic.Basic
import Lean.Parser.Tactic
import Mathlib.Algebra.Field.ZMod
import ZkLean.solve_mle
open Lean Meta Elab Tactic

open Mathlib.Tactic.Valify

private def isArithmeticHead (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some n =>
      n == ``HAdd.hAdd || n == ``Add.add ||
      n == ``HSub.hSub || n == ``Sub.sub ||
      n == ``HMul.hMul || n == ``Mul.mul ||
      n == ``Neg.neg   || n == ``HMod.hMod ||
      n == ``HPow.hPow || n == ``Pow.pow
  | none => false

private def compositeInsideValHere? (e : Expr) : MetaM (Option Expr) := do
  --let e ← whnf e
  if e.isAppOf ``ZMod.val then
    let args := e.getAppArgs

    if let some t := args.back? then
      if isArithmeticHead t then
        logInfo m!"{args}"
        return some e
  pure none

/-- DFS for first subterm of the form `ZMod.val t` where `t` is composite
(arithmetic-headed). -/
partial def firstCompositeInsideVal? (e : Expr) : MetaM (Option Expr) := do
  if let some t ← compositeInsideValHere? e then
    return some t
  match e with
  | .app f a =>
      if let some r ← firstCompositeInsideVal? f then return some r
      firstCompositeInsideVal? a
  | _                   => pure none


partial def pushValToNat (n : Expr) (t : Expr) : MetaM Expr := do
  let head := t.getAppFn
  let args := t.getAppArgs
  match head.constName? with
  | some name =>
    logInfo m!"{name}"
    if name == ``HAdd.hAdd || name == ``Add.add then
      -- binary add: ... a b
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let a' ← pushValToNat n a
      let b' ← pushValToNat n b
      return mkApp2 (mkConst ``Nat.add) a' b'
    else if name == ``HSub.hSub || name == ``Sub.sub then
      -- binary sub: ... a b (literal Nat subtraction)
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let a' ← pushValToNat n a
      let b' ← pushValToNat n b
      return mkApp2 (mkConst ``Nat.sub) a' b'
    else if name == ``HMul.hMul || name == ``Mul.mul then
      -- binary mul: ... a b
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      let a' ← pushValToNat n a
      let b' ← pushValToNat n b
      return mkApp2 (mkConst ``Nat.mul) a' b'
    else
      -- atomic fallback: ZMod.val n t
      return mkApp2 (mkConst ``ZMod.val) n t
  | none =>
      -- not constant-headed; treat as atomic
      return mkApp2 (mkConst ``ZMod.val) n t


def pushValToNatMod (n : Expr) (t : Expr) : MetaM Expr := do
  let e ← pushValToNat n t
  let modExpr ← mkAppM ``HMod.hMod #[e, n]
  return modExpr

/-- `findInsideVal` optionally binds the found composite term:
`findInsideVal` or `findInsideVal => name`. -/
syntax (name := findInsideVal) "findInsideVal" (ppSpace "=>" ident)? : tactic


@[tactic findInsideVal] def evalFindInsideVal : Tactic := fun stx => do
  let g ← getMainGoal
  logInfo m!"{g}"
  let ty ← instantiateMVars (← g.getType)
  let some t ← firstCompositeInsideVal? ty
    | do logInfo "none"; return ()
  let args := t.getAppArgs
  logInfo m!"found: {← ppExpr t}"
  let exp ← pushValToNat args[0]! args[1]!
  let e ← mkAppM ``HMod.hMod #[exp, args[0]!]
  let args2 := args[1]!.getAppApps
  let e2 := args2[args2.size-1]!
  let args3:= e2.getAppArgs
  logInfo m!"NEW ARGS: {e2.getAppArgs}"
  let prop <- mkEq t e
  let pr ←  g.withContext do  mkFreshExprMVar prop


  let rhs := mkApp2 (mkConst ``ZMod.val) args[0]! args3[args3.size -1]!
  let lhs := mkApp2 (mkConst ``ZMod.val) args[0]! args3[args3.size -2]!
  let prop2 <- g.withContext do mkAppM ``LE.le #[rhs, lhs]
  let pr2 ← g.withContext do mkFreshExprMVar prop2
  let hm ← g.withContext do pr.mvarId!.assert `vNat prop2 pr2
  let gWithHyp ← g.withContext do g.assert `vNat prop pr
  let gWithHyp2 <- g.withContext do  gWithHyp.assert `subleq prop2 pr2
  setGoals [pr2.mvarId!, hm, gWithHyp2]



syntax (name := valifyHelper) "valify_helper" ppSpace "[" ident,* "]" : tactic

@[tactic valifyHelper]
elab_rules : tactic
| `(tactic| valify_helper [$hs,*]) => do
  evalTactic (← `(tactic| findInsideVal))
  -- UGH NEED TO FIND THINGS FOR ELIM2_NORM_NUM
  -- valify [h1, h2]
  -- elim2_norm_num h1 h2
  -- simp
  -- intro h
  -- simp [ZMod.val_sub h]
  -- valify [h1, h2]
  -- elim2_norm_num h1 h2
  -- intros hx hy
  -- simp at hy
  -- rw [hy]
  -- simp
  -- rw [Nat.mod_eq_of_lt]
  -- try_apply_lemma_hyps [h1, h2, h3]



  -- match stx with
  -- | `(tactic| findInsideVal => $x) =>
  --     evalTactic (← `(tactic| set $x := ($t)))
  -- | _ => pure ()

-- evalTactic (← `(tactic| apply split_one at $(id1):ident))
--   evalTactic (← `(tactic| apply split_one at $(id2):ident))
--   evalTactic (← `(tactic| apply Or.elim $id1))
--   evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
--   evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
--   try
--       evalTactic (←  `(tactic|apply Nat.le_refl))
--   catch _ => pure ()

--   evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
--   try
--       evalTactic (←  `(tactic|apply Nat.le_refl))
--   catch _ => pure ()
--   evalTactic (← `(tactic| intro hx; apply Or.elim $id2))
--   evalTactic (← `(tactic| intro hy; rewrite [hx]; rewrite [hy]; simp;))
--   try
--       evalTactic (←  `(tactic|apply Nat.le_refl))
--   catch _ => pure ()
--   evalTactic (← `(tactic| intro hy; rewrite [hy]; rewrite [hx]; simp;))
--   try
--       evalTactic (←  `(tactic|apply Nat.le_refl))
--   catch _ => pure ()



example (fv1 fv2 : Vector (ZMod 7) 8): (fv1[0].val <= 1 ) -> (fv2[1].val <= 1 ) -> (fv2[0].val <= 1 ) -> (fv1[0] * fv2[0]* (fv1[0]+fv2[1] - (fv1[0]*fv2[1])) + fv1[0] * fv2[0]).val < 7 := by
  intros h1 h2 h3
  valify [ h1, h2, h3]
  valify_helper []
  --[h1, h2 , h3]
  --findInsideVal
  valify [h1, h2]
  elim2_norm_num h1 h2
  simp
  intro h
  simp [ZMod.val_sub h]
  valify [h1, h2]
  elim2_norm_num h1 h2
  intros hx hy
  simp at hy
  rw [hy]
  simp
  rw [Nat.mod_eq_of_lt]
  try_apply_lemma_hyps [h1, h2, h3]

lemma ugh  (h: x.val <= (1 : ZMod ff).val): ( (1 : ZMod ff) -x).val = ( 1 - x.val) % ff := by sorry

lemma ugh2  (h: x <= 1 ): ( (1 - (x % ff) )% ff )= ( 1 - x ) % ff := by sorry



example (fv : Vector (ZMod ff) 8): (fv[0].val <= 1) -> (fv[1].val <= 1 ) -> (fv[2].val <= 1 ) -> ( (1: ZMod ff) - (fv[0]*fv[1] + (1-fv[0])*(1-fv[1]))).val < 7 := by
  intros h1 h2 h3
  valify [ h1, h2, h3]
  valify_helper []
  --[h1, h2 , h3]
  --findInsideVal
  valify [h1, h2]
  simp
  rw [Nat.mod_eq_of_lt]
  try_apply_lemma_hyps [h1, h2, h3]
  intro h
  simp
  simp [ugh h]

  valify [h1, h2]
  simp
  rw [ugh2]
  try_apply_lemma_hyps [h1, h2, h3]
  intros hx hy
  simp at hy
  rw [hy]
  valify [h1, h2, h3]
  rw [Nat.mod_eq_of_lt]
  try_apply_lemma_hyps [h1, h2, h3]














  --rw [Nat.mod_eq_of_lt]



  -- lemma or_val {n : ℕ} [h: NeZero n] [h': GtTwo n] {x y : ZMod n}
  --   (hx : x.val ≤ 1) (hy : y.val <= 1) :
  -- (x + y - x*y).val =
  -- ((x.val + y.val)  - (x.val * y.val) )% n := by
  -- have h:  (x + y).val >=  (x * y).val := by
  --         simp [ZMod.val_mul]
  --         simp [ZMod.val_add]
  --         apply split_one at hx
  --         apply split_one at hy
  --         apply Or.elim hx
  --         intro hx'
  --         apply Or.elim hy
  --         intro hy'
  --         rw [hx']
  --         rw [hy']
  --         intro hy'
  --         rw [hx']
  --         rw [hy']
  --         simp
  --         intro hx'
  --         apply Or.elim hy
  --         intro hy'
  --         rw [hx']
  --         rw [hy']
  --         simp
  --         intro hy'
  --         rw [hx']
  --         rw [hy']
  --         simp
  --         cases n with
  --           | zero => simp
  --           | succ m => cases m with
  --              | zero => simp
  --              | succ m' => cases m' with
  --                   | zero => simp
  --                             simp at h'
  --                             exact (lt_irrefl 2) h'.out
  --                   | succ n' =>
  --                         have h3 : 3 ≤ n' + 1 + 1 +1 := by simp
  --                         have hlt : 2 < n' + 1 + 1 + 1 := by apply h3
  --                         rw [Nat.mod_eq_of_lt hlt]
  --                         simp
  -- simp [ZMod.val_sub h]
  -- simp [ZMod.val_mul]
  -- simp [ZMod.val_add]
  -- apply split_one at hx
  -- apply split_one at hy
  -- apply Or.elim hx
  -- intro hx'
  -- apply Or.elim hy
  -- intro hy'
  -- rw [hx']
  -- rw [hy']
  -- simp
  -- intro hy'
  -- rw [hx']
  -- rw [hy']
  -- simp
  -- intro hx'
  -- apply Or.elim hy
  -- intro hy'
  -- rw [hx']
  -- rw [hy']
  -- simp
  -- intro hy'
  -- rw [hx']
  -- rw [hy']
  -- simp
  -- cases n with
  --           | zero => simp
  --           | succ m => cases m with
  --              | zero => simp
  --              | succ m' => cases m' with
  --                   | zero => simp
  --                             simp at h'
  --                             exact (lt_irrefl 2) h'.out
  --                   | succ n' =>
  --                         have h3 : 3 ≤ n' + 1 + 1 +1 := by simp
  --                         have hlt : 2 < n' + 1 + 1 + 1 := by apply h3
  --                         rw [Nat.mod_eq_of_lt hlt]
  --                         simp










-- Solution we do a have
--- in the have we move things around how we want them to be
--- and then we do a proof
---- we use simp
