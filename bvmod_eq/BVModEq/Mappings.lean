import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith

namespace BVModEq

class GtTwo (n : ℕ) : Prop where
  out : 2 < n

theorem GtTwo.gt_two [G : GtTwo n] : 2 < n :=
  G.out

def bool_to_bv (n: ℕ) (b: Bool) : (BitVec n) := if b then 1#n else 0#n

def map_bv_to_f {bw} (n: ℕ) (b : BitVec bw) : ZMod n :=
  (b.toNat : ZMod n)

def map_f_to_bv {ff : ℕ} n (rs1_val : ZMod ff) : Option (BitVec n) :=
  let m : ℕ := ZMod.val rs1_val
  if m < 2^n then
    some (BitVec.ofNat n m)
  else
    none

set_option maxHeartbeats 2000000

lemma extract_bv_rel {b: ℕ} {x : ZMod ff} [h0: NeZero b]  :
  some (bool_to_bv b bf) = map_f_to_bv b x
  ↔ (x.val <= 1 ∧ (if bf then 1#b else 0#b) = BitVec.ofNat b x.val)
  := by
  unfold map_f_to_bv
  unfold bool_to_bv
  dsimp
  simp
  intros h
  constructor
  intros hx
  cases a: x.val with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ m =>
      exfalso
      rw [a] at h
      unfold BitVec.ofNat at h
      unfold Fin.Internal.ofNat at h
      have h' := congrArg (fun x => x.toFin.val) h
      simp at h'
      have mod_eq : (m + 2) % (2^b) = m + 2 := by
        rw [← a]
        apply Nat.mod_eq_of_lt
        apply hx
      rw [← h'] at mod_eq
      cases g : bf with
      | true =>
        rw [g] at mod_eq
        simp at mod_eq
        have h1 : 1 % 2 ^ b = 1 := by
          apply Nat.mod_eq_of_lt (Nat.one_lt_two_pow h0.out)
        rw [h1] at mod_eq
        simp at mod_eq
      | false =>
        rw [g] at mod_eq
        simp at mod_eq
  intro h
  apply Nat.lt_of_le_of_lt
  apply h
  apply Nat.one_lt_two_pow h0.out


lemma ZMod.eq_if_val [NeZero ff]  (a b : ZMod ff) :
  (a = b) ↔ (a.val = b.val) := by
  apply Iff.intro
  intros h
  rw [h]
  intros h
  apply ZMod.val_injective at h
  exact h

lemma BitVec_ofNat_eq_iff (n : ℕ) {x y : ℕ} (hx : x < 2^n) (hy : y < 2^n) :
  (x = y) ↔ (BitVec.ofNat n x = BitVec.ofNat n y) := by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.Internal.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^n = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx
