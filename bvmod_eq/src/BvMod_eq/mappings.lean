import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith

namespace BvMod_eq

class GtTwo (n : ℕ) : Prop where
  out : 2 < n

def bool_to_bv (b: Bool) : (BitVec n) := if b then 1 else 0

def map_f_to_bv {ff : ℕ} n (rs1_val : ZMod ff) : Option (BitVec n) :=
  let m : ℕ := ZMod.val rs1_val
  if m < 2^n then
    some (BitVec.ofNat n m)
  else
    none

set_option maxHeartbeats 2000000

lemma extract_bv_rel_8 {x : ZMod ff} :
  some (bool_to_bv bf) = map_f_to_bv 8 x
  ↔ (x.val <= 1 ∧ (if bf then 1#8 else 0#8) = BitVec.ofNat 8 x.val)
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
      unfold Fin.ofNat at h
      have h' := congrArg (fun x => x.toFin.val) h
      simp at h'
      have mod_eq : (m + 2) % 256 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
      rw [← h'] at mod_eq
      cases g : bf with
      | true =>
        rw [g] at mod_eq
        simp at mod_eq
      | false =>
        rw [g] at mod_eq
        simp at mod_eq
  intro h
  linarith

lemma extract_bv_rel_16 (x : ZMod ff) :
  some (bool_to_bv bf) = map_f_to_bv 16 x
  ↔ (x.val <= 1 /\ (if bf then 1#16 else 0#16) = BitVec.ofNat 16 x.val)
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
      unfold Fin.ofNat at h
      have h' := congrArg (fun x => x.toFin.val) h
      simp at h'
      have mod_eq : (m + 2) % 65536 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
      rw [← h'] at mod_eq
      cases g : bf with
      | true =>
        rw [g] at mod_eq
        simp at mod_eq
      | false =>
        rw [g] at mod_eq
        simp at mod_eq
  intro h
  linarith


lemma extract_bv_rel_32 (x: ZMod ff) :
  some (bool_to_bv bf) = map_f_to_bv 32 x
  ↔ (x.val <= 1 /\ (if bf then 1#32 else 0#32) = BitVec.ofNat 32 x.val)
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
      unfold Fin.ofNat at h
      have h' := congrArg (fun x => x.toFin.val) h
      simp at h'
      have mod_eq : (m + 2) % 4294967296 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
      rw [← h'] at mod_eq
      cases g : bf with
      | true =>
        rw [g] at mod_eq
        simp at mod_eq
      | false =>
        rw [g] at mod_eq
        simp at mod_eq
  intro h
  linarith

lemma extract_bv_rel_64 (x: ZMod ff) :
  some (bool_to_bv bf) = map_f_to_bv 64 x
  ↔ (x.val <= 1 /\ (if bf then 1#64 else 0#64) = BitVec.ofNat 64 x.val)
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
      unfold Fin.ofNat at h
      have h' := congrArg (fun x => x.toFin.val) h
      simp at h'
      have mod_eq : (m + 2) % 18446744073709551616 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
      rw [← h'] at mod_eq
      cases g : bf with
      | true =>
        rw [g] at mod_eq
        simp at mod_eq
      | false =>
        rw [g] at mod_eq
        simp at mod_eq
  intro h
  linarith

lemma ZMod.eq_if_val [NeZero ff]  (a b : ZMod ff) :
  (a = b) ↔ (a.val = b.val) := by
  apply Iff.intro
  intros h
  rw [h]
  intros h
  apply ZMod.val_injective at h
  exact h

lemma BitVec_ofNat_eq_iff {x y : ℕ} (hx : x < 2^n) (hy : y < 2^n) :
  (x = y) ↔ (BitVec.ofNat n x = BitVec.ofNat n y) := by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^n = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx
