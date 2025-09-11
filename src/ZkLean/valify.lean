/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis
-/
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Order.Basic
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute
import ZkLean.AST
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import ZkLean.Formalism
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Lean.Elab.Term
import Mathlib.Tactic.Ring
import Std.Tactic.BVDecide
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.Basic
import ZkLean.range_analysis


/-!
# `valify` tactic

Hello :)
```

```
-/

namespace Mathlib.Tactic.Valify



open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic


/-- evalTactic (← `(tactic| apply split_one at $(id1):ident))
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


Hello.
-/
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


--abbrev ff := 4139
-- abbrev f := ZMod ff
-- abbrev b := Nat.log2 ff

class GtTwo (n : ℕ) : Prop where
  out : 2 < n

lemma one_le_two_mod_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ 2 % n := by
  have hlt : 2 < n := Nat.succ_le.mp hn
  simp [Nat.mod_eq_of_lt hlt]


--(1 - fv1[0] - fv2[0] + fv1[0] * fv2[0] + fv1[0] * fv2[0])

 lemma ult_val {n : ℕ} [h: NeZero n]  [h': GtTwo n] {x y : ZMod n}
    (hx : x.val ≤ 1) (hy : y.val <= 1): (1 - x - y + x * y + x * y).val =
    (1 - (x).val + (x).val * (y).val - (y).val + (x).val * (y).val)  := by
    --sorry
    have hz : x*y + (x*y + (1 - x - y)) = (x*y + x*y + (1 - x)) - y := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have k := congrArg ZMod.val hz
    conv =>
      lhs
      simp  [add_comm]
      rw [k]
    haveI : Fact (1 < n) := ⟨(by decide : 1 < 2).trans h'.out⟩
    have hlt: (x * y + x * y + (1 - x)).val >= y.val := by
      simp [ZMod.val_add]
      simp [ZMod.val_mul]
      rw [ZMod.val_sub]
      rw [ZMod.val_one]
      apply split_one at hx
      apply split_one at hy
      apply Or.elim hx
      intro hx'
      apply Or.elim hy
      intro hy'
      rw [hx']
      rw [hy']
      simp
      intro hy'
      rw [hx']
      rw [hy']
      simp
      rw [Nat.mod_eq_of_lt]
      apply this.out
      intro hx'
      apply Or.elim hy
      intro hy'
      rw [hx']
      rw [hy']
      simp
      intro hy'
      rw [hx']
      rw [hy']
      simp
      rw [Nat.mod_eq_of_lt]
      simp
      apply h'.out
      rw [ZMod.val_one]
      apply hx
    rw [ZMod.val_sub ]
    simp [ZMod.val_add]
    simp [ZMod.val_mul]
    rw [ZMod.val_sub]
    rw [ZMod.val_one]

    simp [add_assoc]
    simp [add_left_comm, add_comm]
    apply split_one at hx
    apply split_one at hy
    apply Or.elim hx
    intro hx'
    apply Or.elim hy
    intro hy'
    rw [hx']
    rw [hy']
    rw [Nat.mod_eq_of_lt]
    simp
    norm_num
    apply this.out
    intro hy'
    rw [hx']
    rw [hy']
    simp
    rw [Nat.mod_eq_of_lt]
    apply this.out
    intro hx'
    apply Or.elim hy
    intro hy'
    rw [hx']
    rw [hy']
    simp
    intro hy'
    rw [hx']
    rw [hy']
    simp
    rw [Nat.mod_eq_of_lt]
    apply h'.out
    rw [ZMod.val_one]
    apply hx
    apply hlt

    -- cases n with
    --   | zero => simp
    --             simp at this
    --             apply this.out
    --   | succ m => cases m with
    --             | zero => simp
    --                       simp at h'
    --                       exact (by decide : ¬ 2 < 1) h'.out
    --             | succ n => simp
    -- apply h'.out
    -- rw [ZMod.val_one]
    -- apply hx
    -- apply hlt



lemma one_val {n : ℕ} {x y : ZMod n}
(hx : x.val ≤ 1) :
  (1-x).val =
  (1 - x.val) % n := by
sorry

lemma or_val {n : ℕ} [h: NeZero n] [h': GtTwo n] {x y : ZMod n}
    (hx : x.val ≤ 1) (hy : y.val <= 1) :
  (x + y - x*y).val =
  ((x.val + y.val)  - (x.val * y.val) )% n := by
  have h:  (x + y).val >=  (x * y).val := by
          simp [ZMod.val_mul]
          simp [ZMod.val_add]
          apply split_one at hx
          apply split_one at hy
          apply Or.elim hx
          intro hx'
          apply Or.elim hy
          intro hy'
          rw [hx']
          rw [hy']
          intro hy'
          rw [hx']
          rw [hy']
          simp
          intro hx'
          apply Or.elim hy
          intro hy'
          rw [hx']
          rw [hy']
          simp
          intro hy'
          rw [hx']
          rw [hy']
          simp
          cases n with
            | zero => simp
            | succ m => cases m with
               | zero => simp
               | succ m' => cases m' with
                    | zero => simp
                              simp at h'
                              exact (lt_irrefl 2) h'.out
                    | succ n' =>
                          have h3 : 3 ≤ n' + 1 + 1 +1 := by simp
                          have hlt : 2 < n' + 1 + 1 + 1 := by apply h3
                          rw [Nat.mod_eq_of_lt hlt]
                          simp
  simp [ZMod.val_sub h]
  simp [ZMod.val_mul]
  simp [ZMod.val_add]
  apply split_one at hx
  apply split_one at hy
  apply Or.elim hx
  intro hx'
  apply Or.elim hy
  intro hy'
  rw [hx']
  rw [hy']
  simp
  intro hy'
  rw [hx']
  rw [hy']
  simp
  intro hx'
  apply Or.elim hy
  intro hy'
  rw [hx']
  rw [hy']
  simp
  intro hy'
  rw [hx']
  rw [hy']
  simp
  cases n with
            | zero => simp
            | succ m => cases m with
               | zero => simp
               | succ m' => cases m' with
                    | zero => simp
                              simp at h'
                              exact (lt_irrefl 2) h'.out
                    | succ n' =>
                          have h3 : 3 ≤ n' + 1 + 1 +1 := by simp
                          have hlt : 2 < n' + 1 + 1 + 1 := by apply h3
                          rw [Nat.mod_eq_of_lt hlt]
                          simp


syntax (name := valify) "valify" (simpArgs)? (location)? : tactic



macro_rules
| `(tactic| valify $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic|
    simp only [one_val, ult_val, or_val, ZMod.val_sub, ZMod.val_add, ZMod.val_mul, ZMod.val_one, ZMod.val_ofNat, push_cast, $args,*,] $[at $location]? )



-- name: ZModify

-- /-- The `Simp.Context` generated by `zify`. -/
def mkZifyContext (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ",")) :
    TacticM MkSimpContextResult := do
  let args := simpArgs.map (·.getElems) |>.getD #[]
  mkSimpContext
    (← `(tactic| simp only  [one_val , ult_val, or_val, ZMod.val_sub, ZMod.val_add, ZMod.val_mul, ZMod.val_one, ZMod.val_ofNat, push_cast, $args,*,] )) false

/-- A variant of `applySimpResultToProp` that cannot close the goal, but does not need a meta
variable and returns a tuple of a proof and the corresponding simplified proposition. -/
def applySimpResultToProp' (proof : Expr) (prop : Expr) (r : Simp.Result) : MetaM (Expr × Expr) :=
  do
  match r.proof? with
  | some eqProof => return (← mkExpectedTypeHint (← mkEqMP eqProof proof) r.expr, r.expr)
  | none =>
    if r.expr != prop then
      return (← mkExpectedTypeHint proof r.expr, r.expr)
    else
      return (proof, r.expr)

/-- Translate a proof and the proposition into a zified form. -/
def zifyProof (simpArgs : Option (Syntax.TSepArray `Lean.Parser.Tactic.simpStar ","))
    (proof : Expr) (prop : Expr) : TacticM (Expr × Expr) := do
  let ctx_result ← mkZifyContext simpArgs
  let (r, _) ← simp prop ctx_result.ctx
  applySimpResultToProp' proof prop r



end Valify

end Mathlib.Tactic
