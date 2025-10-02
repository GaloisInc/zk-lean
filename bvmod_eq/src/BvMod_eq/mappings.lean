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


def map_f_to_bv_8 {ff : ℕ} (rs1_val : ZMod ff) : Option (BitVec 8) :=
  let n : ℕ := ZMod.val rs1_val
  if n < 2^8 then
    some (BitVec.ofNat 8 n)
  else
    none


#check map_f_to_bv_8

def map_f_to_bv_16  (rs1_val : ZMod ff) : Option (BitVec 16) :=
  let n := (rs1_val.val : Nat)
  if n < 2^16 then
    some (BitVec.ofNat 16 n)
  else
    none

def map_f_to_bv_32  (rs1_val : ZMod ff) : Option (BitVec 32) :=
  let n := (rs1_val.val : Nat)
  if n < 2^32 then
    some (BitVec.ofNat 32 n)
  else
    none

def map_f_to_bv_64 {ff} (rs1_val : ZMod ff) : Option (BitVec 64) :=
  let n := (rs1_val.val : Nat)
  if n < 2^64 then
    some (BitVec.ofNat 64 n)
  else
    none

set_option maxHeartbeats 2000000


lemma extract_bv_rel_8 {ff}  {bf} {x:ZMod ff}: some (bool_to_bv bf) = map_f_to_bv_8 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#8 else 0#8) = BitVec.ofNat 8 x.val) := by
  unfold map_f_to_bv_8
  unfold bool_to_bv
  dsimp
  simp
  intros h
  constructor
  intros hx
  cases a: x.val with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ m =>
          exfalso
          rw [a] at h
          unfold BitVec.ofNat at h
          unfold Fin.ofNat at h
          have h' := congrArg (fun x => x.toFin.val) h
          simp at h'
          cases g : bf with
            | true =>
              have mod_eq : (m + 2) % 256 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq

            | false =>
              have mod_eq : (m + 2) % 256 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq
  intro h
  linarith


lemma extract_bv_rel_16{bf} (x: ZMod ff) : some (bool_to_bv bf) = map_f_to_bv_16 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#16 else 0#16) = BitVec.ofNat 16 x.val) := by
  unfold map_f_to_bv_16
  unfold bool_to_bv
  dsimp
  simp
  intros h
  constructor
  intros hx
  cases a: x.val with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ m =>
          exfalso
          rw [a] at h
          unfold BitVec.ofNat at h
          unfold Fin.ofNat at h
          have h' := congrArg (fun x => x.toFin.val) h
          simp at h'
          cases g : bf with
            | true =>
              have mod_eq : (m + 2) % 65536= m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq
            | false =>
              have mod_eq : (m + 2) % 65536 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq
  intro h
  linarith


lemma extract_bv_rel_32{bf } (x: ZMod ff) : some (bool_to_bv bf) = map_f_to_bv_32 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#32 else 0#32) = BitVec.ofNat 32 x.val) := by
  unfold map_f_to_bv_32
  unfold bool_to_bv
  dsimp
  simp
  intros h
  constructor
  intros hx
  cases a: x.val with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ m =>
          exfalso
          rw [a] at h
          unfold BitVec.ofNat at h
          unfold Fin.ofNat at h
          have h' := congrArg (fun x => x.toFin.val) h
          simp at h'
          cases g : bf with
            | true =>
              have mod_eq : (m + 2) % 4294967296 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq

            | false =>
              have mod_eq : (m + 2) % 4294967296 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq
  intro h
  linarith


lemma extract_bv_rel_64{bf } (x: ZMod ff): some (bool_to_bv bf) = map_f_to_bv_64 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#64 else 0#64) = BitVec.ofNat 64 x.val) := by
  unfold map_f_to_bv_64
  unfold bool_to_bv
  dsimp
  simp
  intros h
  constructor
  intros hx
  cases a: x.val with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ m =>
          exfalso
          rw [a] at h
          unfold BitVec.ofNat at h
          unfold Fin.ofNat at h
          have h' := congrArg (fun x => x.toFin.val) h
          simp at h'
          cases g : bf with
            | true =>
              have mod_eq : (m + 2) % 18446744073709551616 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq
            | false =>
              have mod_eq : (m + 2) % 18446744073709551616 = m + 2 := Nat.mod_eq_of_lt (by linarith [hx, a])
              rw [← h'] at mod_eq
              rw [g] at mod_eq
              simp at mod_eq
  intro h
  linarith



lemma ZMod.eq_if_val [NeZero ff]  (a b : ZMod ff) :
  (a = b) <-> (a.val = b.val) := by
  apply Iff.intro
  intros h
  rw [h]
  intros h
  apply ZMod.val_injective at h
  exact h


lemma BitVec_ofNat_eq_iff_8 {x y : ℕ} (hx : x < 2^8) (hy : y < 2^8) :
  (x = y) <-> (BitVec.ofNat 8 x = BitVec.ofNat 8 y) := by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^8 = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx

lemma BitVec_ofNat_eq_iff_16 {x y : ℕ} (hx : x < 2^16) (hy : y < 2^16) :
  (x = y) <-> (BitVec.ofNat 16 x = BitVec.ofNat 16 y) := by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^16 = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx


lemma BitVec_ofNat_eq_iff_32 {x y : ℕ} (hx : x < 2^32) (hy : y < 2^32) :
  (x = y) <-> (BitVec.ofNat 32 x = BitVec.ofNat 32 y) := by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^32 = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx

lemma BitVec_ofNat_eq_iff_64 {x y : ℕ} (hx : x < 2^64) (hy : y < 2^64) :
  (x = y)  <-> (BitVec.ofNat 64 x = BitVec.ofNat 64 y):= by
  constructor
  intro h
  rw [h]
  intro h
  unfold BitVec.ofNat at h
  unfold Fin.ofNat at h
  have h' := congrArg (fun x => x.toFin.val) h
  simp at h
  apply Nat.mod_eq_of_modEq at h'
  have hxy : x % 2^64 = y := h' hy
  rw [Nat.mod_eq_of_lt] at hxy
  apply hxy
  apply hx
