import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Control.Fold
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Kleene
import ZkLean
import Std.Data.HashMap.Basic
import Lean.Meta.Basic
import Lean.Elab.Term
--import Mathlib.Tactic.Ring
import Std.Tactic.BVDecide
import Mathlib.Tactic.Linarith
import ZkLean.valify
import ZkLean.range_analysis
import ZkLean.bvify
import Auto.Tactic




open Lean Meta Elab Term
open Std





def bool_to_bv (b: Bool) : (BitVec 8) := if b == true then 1 else 0
--if b == false then 1

instance : Fact (Nat.Prime 4139) := by sorry
instance : ZKField (ZMod 4139) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  chunk_to_bits {num_bits: Nat} f :=
    let bv : BitVec 13 := BitVec.ofFin (Fin.castSucc f)
    -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
        0
    ) (Vector.range num_bits)

instance : Witnessable (ZMod 4139) (ZMod 4139) := by sorry

def map_f_to_bv (rs1_val : ZMod 4139) : Option (BitVec 8) :=
  let n := (rs1_val.val : Nat)
  if n < 2^8 then
    some (BitVec.ofNat 8 n)
  else
    none


abbrev ff := 4139
abbrev f := ZMod ff
abbrev b := Nat.log2 ff

lemma add_le_ff (x y : f) (a b : ℕ):
  ( x.val < a) ∧ (y.val < b) -> (x.val + y.val < a+ b)
  := by intro h1
        apply Nat.add_lt_add h1.left h1.right

lemma trans_range_ff (x y : f) (a b : ℕ):
(x.val + y.val < a + b) ∧ (x + y = z) /\ a+b < ff -> (z.val < a+ b) := by
  rintro ⟨h, h1, h2⟩
  subst h1
  rw [ZMod.val_add]
  rw [Nat.mod_eq_of_lt (h.trans h2)]
  exact h

lemma zmod_to_bitvec_add (x y : f):
    (x.val + y.val < ff) -> BitVec.ofNat b x.val + BitVec.ofNat b y.val = BitVec.ofNat b (x + y).val
    := by
      intro h
      rw [ZMod.val_add, Nat.mod_eq_of_lt h]
      exact (@BitVec.ofNat_add b x.val y.val).symm


lemma zmod_to_bitvec_mul (x y : f):
    (h : x.val * y.val < ff) ->
    BitVec.ofNat b x.val * BitVec.ofNat b y.val
      = BitVec.ofNat b (x * y).val := by
      intro h
      rw [@ZMod.val_mul ff x y, Nat.mod_eq_of_lt h]
      sorry

 -- active TODOs

 lemma BitVec.ofNat_mul {w a b : ℕ} :
  BitVec.ofNat w (a * b) =
    (BitVec.ofNat w a) * (BitVec.ofNat w b) := by
  -- BitVec multiplication is just modulo 2^w
  sorry


theorem ofNat_sub_ofNat_of_le (x y : Nat) (hy : y < 2 ^ w) (hlt : y ≤ x):
    BitVec.ofNat w x - BitVec.ofNat w y = BitVec.ofNat w (x - y) := by
    sorry

lemma bool_to_bv_leads_to_binary (x : f) (bv : BitVec 8) (i : ℕ) (hi : i < 8) :
    some (bool_to_bv bv[i]) = map_f_to_bv x →
    x.val ≤ 1 := by
    sorry
    -- unfold map_f_to_bv
    -- dsimp
    -- split_ifs with leq
    -- intros H
    -- injection H with H
    -- unfold bool_to_bv at H
    -- split_ifs at H
    -- injection H with Hx
    -- injection Hx with Hx'
    -- rw [Nat.mod_eq_of_lt leq] at Hx'
    -- rw [Nat.mod_eq_of_lt] at Hx'
    -- rw [ZMod.val_one]
    -- linarith
    -- simp
    -- injection H with Hx
    -- injection Hx with Hx'
    -- rw [Nat.mod_eq_of_lt leq] at Hx'
    -- rw [Nat.mod_eq_of_lt] at Hx'
    -- rw [←Hx']
    -- simp
    -- rw [ZMod.val_one]
    -- norm_num
    -- simp


-- I need to think more about bounds here..




lemma ZMod.val_drop_mod (a : ZMod ff) (n:ℕ):
 (a.val % ff = a.val) := by
  rw [Nat.mod_eq_of_lt]
  exact ZMod.val_lt a


 lemma ZMod.move_1_sub_bit (a: ZMod ff):
  (a.val < 2)  -> (1-a).val= 1- a.val := by
  intro h
  have h_cases : a.val = 0 ∨ a.val = 1 := by
    cases a.val: a.val with
    | zero => exact Or.inl rfl
    | succ n =>  cases n with
      | zero => exact Or.inr rfl
      | succ m =>
             exfalso
             rw [a.val] at h
             linarith
  cases h_cases with
  | inl h0 => rw [ZMod.val_sub, h0, ZMod.val_one]
              rw [h0, ZMod.val_one]
              norm_num
  | inr h0 => rw [ZMod.val_sub, h0,  ZMod.val_one]
              rw [h0, ZMod.val_one]


lemma ZMod_XOR_drop_mod (a b: ZMod ff) :
   (a.val <= ZMod.val (1 : ZMod ff)) -> (b.val <= ZMod.val (1 : ZMod ff))  -> ( ((1 - a.val) * b.val) % ff + (a.val * (1 - b.val)) % ff) =  (1 - a.val) * b.val + a.val * (1 - b.val)
   := by
   intros ha hb
   rw [ZMod.val_one] at ha hb
   cases a.val : a.val with
   | zero => cases b.val : b.val with
      | zero => simp
      | succ m => cases m: m with
        | zero => simp
        | succ i => exfalso
                    rw[b.val] at hb
                    linarith
   | succ n => cases b.val : b.val with
      | zero => simp
                rw[a.val] at ha
                linarith
      | succ m => simp


lemma bound {x y : ℕ} (hx : x <= 1) (hy : y <= 1) :
  (1 - x) * y + x * (1 - y) ≤ 1 := by

  cases x: x with
    | zero =>
      cases y: y with
        | zero => norm_num
        | succ n => cases n with
          | zero => norm_num
          | succ m => exfalso
                      rw[y] at hy
                      linarith
    | succ n => cases n with
      | zero => norm_num
      | succ m => exfalso
                  rw[x] at hx
                  linarith

lemma BitVec.ofNat_sub{w a b : ℕ} :
  BitVec.ofNat w (a - b) =
    (BitVec.ofNat w a) - (BitVec.ofNat w b) := by
  -- BitVec multiplication is just modulo 2^w
  sorry

 lemma bit_to_bv { a : ℕ} (w : ℕ) :
  (a <= ZMod.val (1 : ZMod ff)) <-> (BitVec.ofNat w a  = 0#w ∨ BitVec.ofNat w a = 1#w)
     := by sorry
  intro ha
  rw [ZMod.val_one] at ha
  cases a : a with
    | zero => norm_num
    | succ n => cases n with
      | zero => right
                simp
      | succ m => exfalso
                  subst a
                  linarith


set_option maxHeartbeats 2000000


--     intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
--     have h2_le: ZMod.val (fv1[0]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[0] bv1 7 (by decide : 7 < 8) h2
--     have h3_le: ZMod.val (fv1[1]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[1] bv1 6 (by decide : 6 < 8) h3
--     have h4_le: ZMod.val (fv1[2]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[2] bv1 5 (by decide : 5 < 8) h4
--     have h5_le: ZMod.val (fv1[3]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[3] bv1 4 (by decide : 4 < 8) h5
--     have h6_le: ZMod.val (fv1[4]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[4] bv1 3 (by decide : 3 < 8) h6
--     have h7_le: ZMod.val (fv1[5]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[5] bv1 2 (by decide : 2 < 8) h7
--     have h8_le: ZMod.val (fv1[6]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[6] bv1 1 (by decide : 1 < 8) h8
--     have h9_le: ZMod.val (fv1[7]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[7] bv1 0 (by decide : 0 < 8) h9
--     have h10_le: ZMod.val (fv2[0]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[0] bv2 7 (by decide : 7 < 8) h10
--     have h11_le: ZMod.val (fv2[1]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[1] bv2 6 (by decide : 6 < 8) h11
--     have h12_le: ZMod.val (fv2[2]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[2] bv2 5 (by decide : 5 < 8) h12
--     have h13_le: ZMod.val (fv2[3]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[3] bv2 4 (by decide : 4 < 8) h13
--     have h14_le: ZMod.val (fv2[4]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[4] bv2 3 (by decide : 3 < 8) h14
--     have h15_le: ZMod.val (fv2[5]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[5] bv2 2 (by decide : 2 < 8) h15
--     have h16_le: ZMod.val (fv2[6]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[6] bv2 1 (by decide : 1 < 8) h16
--     have h17_le: ZMod.val (fv2[7]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[7] bv2 0 (by decide : 0 < 8) h17
--     --rw [split_cases_ff] at h2_le h3_le h4_le h5_le h6_le h7_le h8_le h9_le h10_le h11_le h12_le h13_le  h14_le h15_le h16_le h17_le
--     rw [map_f_to_bv] at h1
--     dsimp at h1
--     split_ifs at h1 with h
--     injection h1 with h1'
--    -- rw [h1']
--     --
--     --let r1 := (ZMod.val (evalSubtable XOR_16 (fv1.append fv2)))
--     unfold XOR_16
--     unfold evalSubtable
--     simp
--     unfold subtableFromMLE
--     simp
--     unfold Vector.append
--     simp
--     rw [ZMod.eq_iff_val_bv]
--     simp [ZMod.val_add]
--     simp [ZMod.val_mul]
--     simp [ZMod.val_add]
--     simp [ZMod.val_mul]
--     simp [ZMod.val_sub h2_le]
--     simp [ZMod.val_sub h3_le]
--     simp [ZMod.val_sub h4_le]
--     simp [ZMod.val_sub h5_le]
--     simp [ZMod.val_sub h6_le]
--     simp [ZMod.val_sub h7_le]
--     simp [ZMod.val_sub h8_le]
--     simp [ZMod.val_sub h9_le]
--     simp [ZMod.val_sub h10_le]
--     simp [ZMod.val_sub h11_le]
--     simp [ZMod.val_sub h12_le]
--     simp [ZMod.val_sub h13_le]
--     simp [ZMod.val_sub h14_le]
--     simp [ZMod.val_sub h15_le]
--     simp [ZMod.val_sub h16_le]
--     simp [ZMod.val_sub h17_le]
--     simp [ZMod.val_ofNat]
--     simp [ZMod.val_one]
--     norm_num
--     have h0_ineq : (1 - ZMod.val fv1[0]) * ZMod.val fv2[0] + ZMod.val fv1[0] * (1 - ZMod.val fv2[0]) ≤ 1 := by apply xor_sum_bound h2_le h10_le
--     have h1_ineq : (1 - ZMod.val fv1[1]) * ZMod.val fv2[1] + ZMod.val fv1[1] * (1 - ZMod.val fv2[1]) ≤ 1 := by apply xor_sum_bound h3_le h11_le
--     have h2_ineq : (1 - ZMod.val fv1[2]) * ZMod.val fv2[2] + ZMod.val fv1[2] * (1 - ZMod.val fv2[2]) ≤ 1 := by apply xor_sum_bound h4_le h12_le
--     have h3_ineq : (1 - ZMod.val fv1[3]) * ZMod.val fv2[3] + ZMod.val fv1[3] * (1 - ZMod.val fv2[3]) ≤ 1 := by apply xor_sum_bound h5_le h13_le
--     have h4_ineq : (1 - ZMod.val fv1[4]) * ZMod.val fv2[4] + ZMod.val fv1[4] * (1 - ZMod.val fv2[4]) ≤ 1 := by apply xor_sum_bound h6_le h14_le
--     have h5_ineq : (1 - ZMod.val fv1[5]) * ZMod.val fv2[5] + ZMod.val fv1[5] * (1 - ZMod.val fv2[5]) ≤ 1 := by apply xor_sum_bound h7_le h15_le
--     have h6_ineq : (1 - ZMod.val fv1[6]) * ZMod.val fv2[6] + ZMod.val fv1[6] * (1 - ZMod.val fv2[6]) ≤ 1 := by apply xor_sum_bound h8_le h16_le
--     have h7_ineq : (1 - ZMod.val fv1[7]) * ZMod.val fv2[7] + ZMod.val fv1[7] * (1 - ZMod.val fv2[7]) ≤ 1 := by apply xor_sum_bound h9_le h17_le
--     have hlt :
--     ((1 - ZMod.val fv1[7]) * ZMod.val fv2[7] + ZMod.val fv1[7] * (1 - ZMod.val fv2[7]) +
--       2 * ((1 - ZMod.val fv1[6]) * ZMod.val fv2[6] + ZMod.val fv1[6] * (1 - ZMod.val fv2[6])) +
--       4 * ((1 - ZMod.val fv1[5]) * ZMod.val fv2[5] + ZMod.val fv1[5] * (1 - ZMod.val fv2[5])) +
--       8 * ((1 - ZMod.val fv1[4]) * ZMod.val fv2[4] + ZMod.val fv1[4] * (1 - ZMod.val fv2[4])) +
--       16 * ((1 - ZMod.val fv1[3]) * ZMod.val fv2[3] + ZMod.val fv1[3] * (1 - ZMod.val fv2[3])) +
--       32 * ((1 - ZMod.val fv1[2]) * ZMod.val fv2[2] + ZMod.val fv1[2] * (1 - ZMod.val fv2[2])) +
--       64 * ((1 - ZMod.val fv1[1]) * ZMod.val fv2[1] + ZMod.val fv1[1] * (1 - ZMod.val fv2[1])) +
--       128 * ((1 - ZMod.val fv1[0]) * ZMod.val fv2[0] + ZMod.val fv1[0] * (1 - ZMod.val fv2[0]))) <= 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 := by
--          linarith [h0_ineq, h1_ineq, h2_ineq, h3_ineq, h4_ineq, h5_ineq, h6_ineq, h7_ineq]
--     simp at hlt
--     rw [ZMod_XOR_drop_mod fv1[7] fv2[7] h9_le h17_le]
--     rw [ZMod_XOR_drop_mod fv1[6] fv2[6] h8_le h16_le]
--     rw [ZMod_XOR_drop_mod fv1[5] fv2[5] h7_le h15_le]
--     rw [ZMod_XOR_drop_mod fv1[4] fv2[4] h6_le h14_le]
--     rw [ZMod_XOR_drop_mod fv1[3] fv2[3] h5_le h13_le]
--     rw [ZMod_XOR_drop_mod fv1[2] fv2[2] h4_le h12_le]
--     rw [ZMod_XOR_drop_mod fv1[1] fv2[1] h3_le h11_le]
--     --rw [ZMod_XOR_drop_mod fv1[0] fv2[0] h2_le h10_le]
--     rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h0_ineq (by norm_num))]
--     rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 64 h1_ineq) (by norm_num))]
--     rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 32 h2_ineq) (by norm_num))]
--     rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 16 h3_ineq) (by norm_num))]
--     rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 8 h4_ineq) (by norm_num))]
--     rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 4 h5_ineq) (by norm_num))]
--     rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 2 h6_ineq) (by norm_num))]
--     rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hlt (by norm_num))]
--     simp [BitVec.ofNat_add]
--     simp [BitVec.ofNat_mul]
--     simp [BitVec.ofNat_sub]
--     simp [BitVec.ofNat_add]
--     simp [BitVec.ofNat_mul]
--     simp [BitVec.ofNat_sub]
--     rw [bit_to_bv 8] at h2_le h3_le h4_le h5_le h6_le h7_le h8_le h9_le h10_le h11_le h12_le h13_le h14_le h15_le h16_le h17_le
--     unfold map_f_to_bv at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
--     dsimp at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
--     split_ifs at h2 h3 h4 h5
--     split_ifs at h6 h7 h8 h9
--     split_ifs at h10 h11 h12 h13
--     split_ifs at h14 h15 h16 h17
--     simp at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
--     unfold bool_to_bv at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
--     set a := foutput.val
--     set b10:= ZMod.val fv1[0]
--     set b11 := ZMod.val fv1[1]
--     set b12 := ZMod.val fv1[2]
--     set b13 := ZMod.val fv1[3]
--     set b14 := ZMod.val fv1[4]
--     set b15 := ZMod.val fv1[5]
--     set b16 := ZMod.val fv1[6]
--     set b17 := ZMod.val fv1[7]
--     set b20:= ZMod.val fv2[0]
--     set b21 := ZMod.val fv2[1]
--     set b22 := ZMod.val fv2[2]
--     set b23 := ZMod.val fv2[3]
--     set b24 := ZMod.val fv2[4]
--     set b25 := ZMod.val fv2[5]
--     set b26 := ZMod.val fv2[6]
--     set b27 := ZMod.val fv2[7]
--     bv_normalize
--     bv_decide



-- ----------------------------------------------
-- ---- EQ THEOREM -----------------
-- def EQ_16 [Field f] : Subtable f 16 :=
--   subtableFromMLE (fun x => 1*(x[0]*x[8] + (1 - x[0])*(1 - x[8]))*(x[1]*x[9] + (1 - x[1])*(1 - x[9]))*(x[2]*x[10] + (1 - x[2])*(1 - x[10]))*(x[3]*x[11] + (1 - x[3])*(1 - x[11]))*(x[4]*x[12] + (1 - x[4])*(1 - x[12]))*(x[5]*x[13] + (1 - x[5])*(1 - x[13]))*(x[6]*x[14] + (1 - x[6])*(1 - x[14]))*(x[7]*x[15] + (1 - x[7])*(1 - x[15])))

-- lemma eq_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
--   some bvoutput = map_f_to_bv foutput ->
--    some (bool_to_bv bv1[7])  = map_f_to_bv fv1[0]  ->
--    some (bool_to_bv bv1[6]) = map_f_to_bv fv1[1]  ->
--    some (bool_to_bv bv1[5]) = map_f_to_bv fv1[2]  ->
--    some (bool_to_bv bv1[4]) = map_f_to_bv fv1[3]  ->
--    some (bool_to_bv bv1[3]) = map_f_to_bv fv1[4]  ->
--   some (bool_to_bv bv1[2]) = map_f_to_bv fv1[5]  ->
--    some (bool_to_bv bv1[1]) = map_f_to_bv fv1[6]  ->
--    some (bool_to_bv bv1[0]) = map_f_to_bv fv1[7]  ->
--   some (bool_to_bv bv2[7]) = map_f_to_bv fv2[0]  ->
--   some (bool_to_bv bv2[6]) = map_f_to_bv fv2[1]  ->
--   some (bool_to_bv bv2[5]) = map_f_to_bv fv2[2]  ->
--   some (bool_to_bv bv2[4]) = map_f_to_bv fv2[3]  ->
--   some (bool_to_bv bv2[3]) = map_f_to_bv fv2[4]  ->
--   some (bool_to_bv bv2[2]) = map_f_to_bv fv2[5]  ->
--   some (bool_to_bv bv2[1]) = map_f_to_bv fv2[6]  ->
--   some (bool_to_bv bv2[0]) = map_f_to_bv fv2[7]  ->
--   (bvoutput = bool_to_bv (bv1 == bv2))
--   =
--   (foutput = evalSubtable EQ_16 (Vector.append fv1 fv2))
--  := by
--     intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
--     have h2_le: ZMod.val (fv1[0]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[0] bv1 7 (by decide : 7 < 8) h2
--     have h3_le: ZMod.val (fv1[1]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[1] bv1 6 (by decide : 6 < 8) h3
--     have h4_le: ZMod.val (fv1[2]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[2] bv1 5 (by decide : 5 < 8) h4
--     have h5_le: ZMod.val (fv1[3]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[3] bv1 4 (by decide : 4 < 8) h5
--     have h6_le: ZMod.val (fv1[4]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[4] bv1 3 (by decide : 3 < 8) h6
--     have h7_le: ZMod.val (fv1[5]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[5] bv1 2 (by decide : 2 < 8) h7
--     have h8_le: ZMod.val (fv1[6]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[6] bv1 1 (by decide : 1 < 8) h8
--     have h9_le: ZMod.val (fv1[7]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv1[7] bv1 0 (by decide : 0 < 8) h9
--     have h10_le: ZMod.val (fv2[0]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[0] bv2 7 (by decide : 7 < 8) h10
--     have h11_le: ZMod.val (fv2[1]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[1] bv2 6 (by decide : 6 < 8) h11
--     have h12_le: ZMod.val (fv2[2]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[2] bv2 5 (by decide : 5 < 8) h12
--     have h13_le: ZMod.val (fv2[3]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[3] bv2 4 (by decide : 4 < 8) h13
--     have h14_le: ZMod.val (fv2[4]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[4] bv2 3 (by decide : 3 < 8) h14
--     have h15_le: ZMod.val (fv2[5]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[5] bv2 2 (by decide : 2 < 8) h15
--     have h16_le: ZMod.val (fv2[6]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[6] bv2 1 (by decide : 1 < 8) h16
--     have h17_le: ZMod.val (fv2[7]) ≤ ZMod.val (1 : ZMod ff) := bool_to_bv_leads_to_binary fv2[7] bv2 0 (by decide : 0 < 8) h17
--     --rw [split_cases_ff] at h2_le h3_le h4_le h5_le h6_le h7_le h8_le h9_le h10_le h11_le h12_le h13_le  h14_le h15_le h16_le h17_le
--     unfold map_f_to_bv at h1
--     dsimp at h1
--     split_ifs at h1 with h
--     injection h1 with h1'
--     rw [h1']
--     rw [ZMod.eq_iff_val_bv]
--     unfold EQ_16
--     unfold evalSubtable
--     simp
--     unfold subtableFromMLE
--     simp
--     unfold Vector.append
--     simp
--     sorry

lemma extract_bv_rel{bf x} : some (bool_to_bv bf) = map_f_to_bv x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#8 else 0#8) = BitVec.ofNat 8 x.val) := by
  unfold map_f_to_bv
  unfold bool_to_bv
  dsimp
  simp
  intros h
  cases a : x.val with
    | zero => norm_num
    | succ n => cases n with
      | zero => norm_num
      | succ m => exfalso
                  rw [a] at h
                  cases g : bf with
                    | true =>
                      rw [g] at h
                      simp at h
                      rw [BitVec.ofNat] at h
                      injection h with h_eq
                      dsimp at h_eq
                      norm_cast at h_eq
                      zify at h_eq
                      simp at h_eq
                      sorry
                    | false =>
                      sorry


lemma ZMod.eq_if_val (a b : ZMod ff) :
  (a = b ) <->  a.val = b.val := by
  apply Iff.intro
  intros h
  rw [h]
  intros h
  apply ZMod.val_injective at h
  exact h


lemma BitVec.ofNat_eq_iff {x y : ℕ} (hx : x < 2^8) (hy : y < 2^8) :
  (x = y)  <-> (BitVec.ofNat 8 x = BitVec.ofNat 8 y):= by
  sorry

def AND_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*x[7]*x[15] + 2*x[6]*x[14] + 4*x[5]*x[13] + 8*x[4]*x[12] + 16*x[3]*x[11] + 32*x[2]*x[10] + 64*x[1]*x[9] + 128*x[0]*x[8])



lemma and_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = map_f_to_bv foutput ->
   some (bool_to_bv bv1[7])  = map_f_to_bv fv1[0]  ->
   some (bool_to_bv bv1[6]) = map_f_to_bv fv1[1]  ->
   some (bool_to_bv bv1[5]) = map_f_to_bv fv1[2]  ->
   some (bool_to_bv bv1[4]) = map_f_to_bv fv1[3]  ->
   some (bool_to_bv bv1[3]) = map_f_to_bv fv1[4]  ->
  some (bool_to_bv bv1[2]) = map_f_to_bv fv1[5]  ->
   some (bool_to_bv bv1[1]) = map_f_to_bv fv1[6]  ->
   some (bool_to_bv bv1[0]) = map_f_to_bv fv1[7]  ->
  some (bool_to_bv bv2[7]) = map_f_to_bv fv2[0]  ->
  some (bool_to_bv bv2[6]) = map_f_to_bv fv2[1]  ->
  some (bool_to_bv bv2[5]) = map_f_to_bv fv2[2]  ->
  some (bool_to_bv bv2[4]) = map_f_to_bv fv2[3]  ->
  some (bool_to_bv bv2[3]) = map_f_to_bv fv2[4]  ->
  some (bool_to_bv bv2[2]) = map_f_to_bv fv2[5]  ->
  some (bool_to_bv bv2[1]) = map_f_to_bv fv2[6]  ->
  some (bool_to_bv bv2[0]) = map_f_to_bv fv2[7]  ->
  (bvoutput = bv1 &&& bv2)
  =
  (foutput = evalSubtable AND_16 (Vector.append fv1 fv2))
 := by
    -- set up hypothesis
    intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [extract_bv_rel] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rcases h2 with ⟨h2_1, h2_2⟩
    rcases h3 with ⟨h3_1, h3_2⟩
    rcases h4 with ⟨h4_1, h4_2⟩
    rcases h5 with ⟨h5_1, h5_2⟩
    rcases h6 with ⟨h6_1, h6_2⟩
    rcases h7 with ⟨h7_1, h7_2⟩
    rcases h8 with ⟨h8_1, h8_2⟩
    rcases h9 with ⟨h9_1, h9_2⟩
    rcases h10 with ⟨h10_1, h10_2⟩
    rcases h11 with ⟨h11_1, h11_2⟩
    rcases h12 with ⟨h12_1, h12_2⟩
    rcases h13 with ⟨h13_1, h13_2⟩
    rcases h14 with ⟨h14_1, h14_2⟩
    rcases h15 with ⟨h15_1, h15_2⟩
    rcases h16 with ⟨h16_1, h16_2⟩
    rcases h17 with ⟨h17_1, h17_2⟩
    unfold map_f_to_bv at h1
    simp at h1
    rcases h1 with ⟨h1_1, h1_2⟩
    -- apply val and unfold subtables
    rw [ZMod.eq_if_val]
    unfold AND_16
    unfold evalSubtable
    simp
    unfold subtableFromMLE
    simp
    unfold Vector.append
    simp
    --- zmod to nat
    valify
    simp
    rw [Nat.mod_eq_of_lt]
    rw [BitVec.ofNat_eq_iff]
    -- apply bv and nat to zmod
    bvify
    -- necessary because of Lean version this can do away
    set a := foutput.val
    set b10:= ZMod.val fv1[0]
    set b11 := ZMod.val fv1[1]
    set b12 := ZMod.val fv1[2]
    set b13 := ZMod.val fv1[3]
    set b14 := ZMod.val fv1[4]
    set b15 := ZMod.val fv1[5]
    set b16 := ZMod.val fv1[6]
    set b17 := ZMod.val fv1[7]
    set b20:= ZMod.val fv2[0]
    set b21 := ZMod.val fv2[1]
    set b22 := ZMod.val fv2[2]
    set b23 := ZMod.val fv2[3]
    set b24 := ZMod.val fv2[4]
    set b25 := ZMod.val fv2[5]
    set b26 := ZMod.val fv2[6]
    set b27 := ZMod.val fv2[7]
    bv_normalize
    bv_decide
    exact h1_1
    --norm_num
    --- range analysis tactic
    try_apply_lemma_hyps [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_2]
    try_apply_lemma_hyps [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_2]

    -- it is dumb that we have to do this twice maybe we can have some sort of lemma that combines the two different rewrites that assume?




def bf : BitVec 8 := 0
#eval bf[0]
-- in lean 0 == false :)


def XOR_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*((1 - x[7])*x[15] + x[7]*(1 - x[15])) + 2*((1 - x[6])*x[14] + x[6]*(1 - x[14])) + 4*((1 - x[5])*x[13] + x[5]*(1 - x[13])) + 8*((1 - x[4])*x[12] + x[4]*(1 - x[12])) + 16*((1 - x[3])*x[11] + x[3]*(1 - x[11])) + 32*((1 - x[2])*x[10] + x[2]*(1 - x[10])) + 64*((1 - x[1])*x[9] + x[1]*(1 - x[9])) + 128*((1 - x[0])*x[8] + x[0]*(1 - x[8])))

def XOR_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (XOR_16, 0), (XOR_16, 1), (XOR_16, 2), (XOR_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*256*x[2] + 1*256*256*x[1] + 1*256*256*256*x[0])


set_option auto.smt true

lemma xor_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = map_f_to_bv foutput ->
   some (bool_to_bv bv1[7])  = map_f_to_bv fv1[0]  ->
   some (bool_to_bv bv1[6]) = map_f_to_bv fv1[1]  ->
   some (bool_to_bv bv1[5]) = map_f_to_bv fv1[2]  ->
   some (bool_to_bv bv1[4]) = map_f_to_bv fv1[3]  ->
   some (bool_to_bv bv1[3]) = map_f_to_bv fv1[4]  ->
   some (bool_to_bv bv1[2]) = map_f_to_bv fv1[5]  ->
   some (bool_to_bv bv1[1]) = map_f_to_bv fv1[6]  ->
   some (bool_to_bv bv1[0]) = map_f_to_bv fv1[7]  ->
  some (bool_to_bv bv2[7]) = map_f_to_bv fv2[0]  ->
  some (bool_to_bv bv2[6]) = map_f_to_bv fv2[1]  ->
  some (bool_to_bv bv2[5]) = map_f_to_bv fv2[2]  ->
  some (bool_to_bv bv2[4]) = map_f_to_bv fv2[3]  ->
  some (bool_to_bv bv2[3]) = map_f_to_bv fv2[4]  ->
  some (bool_to_bv bv2[2]) = map_f_to_bv fv2[5]  ->
  some (bool_to_bv bv2[1]) = map_f_to_bv fv2[6]  ->
  some (bool_to_bv bv2[0]) = map_f_to_bv fv2[7]  ->
  (bvoutput = BitVec.xor bv1 bv2)
  =
  (foutput = evalSubtable XOR_16 (Vector.append fv1 fv2))
:= by
   -- set up hypothesis
    intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [extract_bv_rel] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rcases h2 with ⟨h2_1, h2_2⟩
    rcases h3 with ⟨h3_1, h3_2⟩
    rcases h4 with ⟨h4_1, h4_2⟩
    rcases h5 with ⟨h5_1, h5_2⟩
    rcases h6 with ⟨h6_1, h6_2⟩
    rcases h7 with ⟨h7_1, h7_2⟩
    rcases h8 with ⟨h8_1, h8_2⟩
    rcases h9 with ⟨h9_1, h9_2⟩
    rcases h10 with ⟨h10_1, h10_2⟩
    rcases h11 with ⟨h11_1, h11_2⟩
    rcases h12 with ⟨h12_1, h12_2⟩
    rcases h13 with ⟨h13_1, h13_2⟩
    rcases h14 with ⟨h14_1, h14_2⟩
    rcases h15 with ⟨h15_1, h15_2⟩
    rcases h16 with ⟨h16_1, h16_2⟩
    rcases h17 with ⟨h17_1, h17_2⟩
    unfold map_f_to_bv at h1
    simp at h1
    rcases h1 with ⟨h1_1, h1_2⟩
    -- apply val and unfold subtables
    rw [ZMod.eq_if_val]
    unfold XOR_16
    unfold evalSubtable
    simp
    unfold subtableFromMLE
    simp
    unfold Vector.append
    simp
    --- zmod to nat
    valify [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_1]
    simp
    rw [Nat.mod_eq_of_lt]
    rw [BitVec.ofNat_eq_iff]
    -- apply bv and nat to zmod
    bvify
    -- necessary because of Lean version this can do away
    set a := foutput.val
    set b10:= ZMod.val fv1[0]
    set b11 := ZMod.val fv1[1]
    set b12 := ZMod.val fv1[2]
    set b13 := ZMod.val fv1[3]
    set b14 := ZMod.val fv1[4]
    set b15 := ZMod.val fv1[5]
    set b16 := ZMod.val fv1[6]
    set b17 := ZMod.val fv1[7]
    set b20:= ZMod.val fv2[0]
    set b21 := ZMod.val fv2[1]
    set b22 := ZMod.val fv2[2]
    set b23 := ZMod.val fv2[3]
    set b24 := ZMod.val fv2[4]
    set b25 := ZMod.val fv2[5]
    set b26 := ZMod.val fv2[6]
    set b27 := ZMod.val fv2[7]
    bv_normalize
    bv_decide
    exact h1_1
    --- range analysis tactic
    auto
    --try_apply_lemma_hyps [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_1]
    try_apply_lemma_hyps [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_1]

    -- it is dumb that we have to do this twice maybe we can have some sort of lemma that combines the two different rewrites that assume?

   #eval 1 * 1 + 1 * 1 + 2 * (1 * 1 + 1 * 1) + 4 * (1 * 1 + 1 * 1) + 8 * (1 * 1 + 1 * 1) + 16 * (1 * 1 + 1 * 1) +
        32 * (1 * 1 + 1 * 1) +
      64 * (1 * 1 + 1 * 1) +
    128 * (1 * 1 + 1 * 1)


#eval 1 * 1 + 1 * 1 + 2 * (1 * 1 + 1 * 1) + 4 * (1 * 1 + 1 * 1) + 8 * (1 * 1 + 1 * 1) + 16 * (1 * 1 + 1 * 1) +
        32 * (1 * 1 + 1 * 1) +
      64 * (1 * 1 + 1 * 1) +
    128 * (1 * 1 + 1 * 1)

#eval  1 * 1 + 2 * 1 * 1 + 4 * 1 * 1 + 8 * 1 * 1 + 16 * 1 * 1 + 32 * 1 * 1 + 64 * 1 * 1 + 128 * 1 * 1 < 2 ^ 8


 def EQ_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(x[0]*x[8] + (1 - x[0])*(1 - x[8]))*(x[1]*x[9] + (1 - x[1])*(1 - x[9]))*(x[2]*x[10] + (1 - x[2])*(1 - x[10]))*(x[3]*x[11] + (1 - x[3])*(1 - x[11]))*(x[4]*x[12] + (1 - x[4])*(1 - x[12]))*(x[5]*x[13] + (1 - x[5])*(1 - x[13]))*(x[6]*x[14] + (1 - x[6])*(1 - x[14]))*(x[7]*x[15] + (1 - x[7])*(1 - x[15])))

lemma eq_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
  some bvoutput = map_f_to_bv foutput ->
   some (bool_to_bv bv1[7])  = map_f_to_bv fv1[0]  ->
   some (bool_to_bv bv1[6]) = map_f_to_bv fv1[1]  ->
   some (bool_to_bv bv1[5]) = map_f_to_bv fv1[2]  ->
   some (bool_to_bv bv1[4]) = map_f_to_bv fv1[3]  ->
   some (bool_to_bv bv1[3]) = map_f_to_bv fv1[4]  ->
  some (bool_to_bv bv1[2]) = map_f_to_bv fv1[5]  ->
   some (bool_to_bv bv1[1]) = map_f_to_bv fv1[6]  ->
   some (bool_to_bv bv1[0]) = map_f_to_bv fv1[7]  ->
  some (bool_to_bv bv2[7]) = map_f_to_bv fv2[0]  ->
  some (bool_to_bv bv2[6]) = map_f_to_bv fv2[1]  ->
  some (bool_to_bv bv2[5]) = map_f_to_bv fv2[2]  ->
  some (bool_to_bv bv2[4]) = map_f_to_bv fv2[3]  ->
  some (bool_to_bv bv2[3]) = map_f_to_bv fv2[4]  ->
  some (bool_to_bv bv2[2]) = map_f_to_bv fv2[5]  ->
  some (bool_to_bv bv2[1]) = map_f_to_bv fv2[6]  ->
  some (bool_to_bv bv2[0]) = map_f_to_bv fv2[7]  ->
  (bvoutput = bool_to_bv (bv1 == bv2))
  =
  (foutput = evalSubtable EQ_16 (Vector.append fv1 fv2))
 := by
    intros h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rw [extract_bv_rel] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    rcases h2 with ⟨h2_1, h2_2⟩
    rcases h3 with ⟨h3_1, h3_2⟩
    rcases h4 with ⟨h4_1, h4_2⟩
    rcases h5 with ⟨h5_1, h5_2⟩
    rcases h6 with ⟨h6_1, h6_2⟩
    rcases h7 with ⟨h7_1, h7_2⟩
    rcases h8 with ⟨h8_1, h8_2⟩
    rcases h9 with ⟨h9_1, h9_2⟩
    rcases h10 with ⟨h10_1, h10_2⟩
    rcases h11 with ⟨h11_1, h11_2⟩
    rcases h12 with ⟨h12_1, h12_2⟩
    rcases h13 with ⟨h13_1, h13_2⟩
    rcases h14 with ⟨h14_1, h14_2⟩
    rcases h15 with ⟨h15_1, h15_2⟩
    rcases h16 with ⟨h16_1, h16_2⟩
    rcases h17 with ⟨h17_1, h17_2⟩
    unfold map_f_to_bv at h1
    simp at h1
    rcases h1 with ⟨h1_1, h1_2⟩
    -- apply val and unfold subtables
    rw [ZMod.eq_if_val]
    unfold EQ_16
    unfold evalSubtable
    unfold bool_to_bv
    simp
    unfold subtableFromMLE
    simp
    unfold Vector.append
    simp
    --- zmod to nat
    valify [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_1]
    simp
    rw [Nat.mod_eq_of_lt]
    rw [BitVec.ofNat_eq_iff]
    -- apply bv and nat to zmod
    bvify
    -- necessary because of Lean version this can do away
    set a := foutput.val
    set b10:= ZMod.val fv1[0]
    set b11 := ZMod.val fv1[1]
    set b12 := ZMod.val fv1[2]
    set b13 := ZMod.val fv1[3]
    set b14 := ZMod.val fv1[4]
    set b15 := ZMod.val fv1[5]
    set b16 := ZMod.val fv1[6]
    set b17 := ZMod.val fv1[7]
    set b20:= ZMod.val fv2[0]
    set b21 := ZMod.val fv2[1]
    set b22 := ZMod.val fv2[2]
    set b23 := ZMod.val fv2[3]
    set b24 := ZMod.val fv2[4]
    set b25 := ZMod.val fv2[5]
    set b26 := ZMod.val fv2[6]
    set b27 := ZMod.val fv2[7]
    bv_normalize
    bv_decide
    --bv_decide
    exact h1_1
    --- range analysis tactic
    sorry
    try_apply_lemma_hyps [h2_1, h3_1, h4_1, h5_1, h6_1, h7_1, h8_1, h9_1, h10_1, h11_1, h12_1, h13_1, h14_1, h15_1, h16_1, h17_1, h16_1]


#eval (1 * 1 + 1 * 1) * (1 * 1 + 1 * 1) * (1 * 1 + 1 * 1) * (1 * 1 + 1 * 1) * (1 * 1 + 1 * 1) * (1 * 1 + 1 * 1) *
      (1 * 1 + 1 * 1) *
    (1 * 1 + 1 * 1)


#eval 1*(1*1 + (1 - 1)*(1 -1))*(1*1 + (1 - 1)*(1 - 1))*(1*1 + (1 - 1)*(1 - 1))*(1*1+ (1 - 1)*(1 - 1))*(1*1 + (1 - 1)*(1 - 1))*(1*1 + (1 - 1)*(1 - 1))*(1*1 + (1 - 1)*(1 - 1))*(1*1 + (1 - 1)*(1 - 1))


def bf1 : BitVec 8 := 1
def bf2 : BitVec 8 := 1

#eval (bool_to_bv ( bf1 = bf2))


-- Different examples ZMod, natural numbers, integers
-- auto fails on all of them
-- linarith succeeds on all
set_option auto.smt true
example (x: ZMod 4139) (x: ZMod 4139) (h1: ZMod.val x  <= 1) (h2: ZMod.val y <= 1) :
  (ZMod.val x+ ZMod.val y) <= 2:= by
  auto
  linarith


example (x:ℕ)  (y:ℕ) (h1: x  <= 1) (h2: y <= 1) :
  (x+ y) <= 3:= by
  auto
  linarith

example (x:Int)  (y:Int) (h1: x <= 1) (h2: y <= 1) :
  (x+ y) <= 3:= by
  auto
  linarith

-- non linear so linarith fails
example (x: ZMod 4139) (x: ZMod 4139) (h1: ZMod.val x  <= 1) (h2: ZMod.val y <= 1) :
  (ZMod.val y)*(1- ZMod.val x)+ (ZMod.val x)*(1-ZMod.val y) <= 1:= by
  --auto
  --linarith
  --ring_nf
  --omega
