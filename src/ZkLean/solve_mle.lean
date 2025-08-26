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


abbrev ff := 17179869203
abbrev f := ZMod ff
abbrev b := Nat.log2 ff

open Lean Meta Elab Tactic


def bool_to_bv (b: Bool) : (BitVec 8) := if b == true then 1 else 0
--if b == false then 1

def bool_to_bv_16 (b: Bool) : (BitVec 16) := if b == true then 1 else 0
--if b == false then 1

def bool_to_bv_32 (b: Bool) : (BitVec 32) := if b == true then 1 else 0
--if b == false then 1

instance : Fact (Nat.Prime ff) := by sorry
instance : ZKField (ZMod ff) where
  hash x :=
    match x.val with
    | 0 => 0
    | n + 1 => hash n

  chunk_to_bits {num_bits: Nat} f :=
    let bv : BitVec 16 := BitVec.ofFin (Fin.castSucc f)
    -- TODO: Double check the endianess.
    Vector.map (fun i =>
      if _:i < 3 then
        if bv[i] then 1 else 0
      else
        0
    ) (Vector.range num_bits)

instance : Witnessable (ZMod ff) (ZMod ff) := by sorry

open Mathlib.Tactic.Valify

instance NotTwo: GtTwo (ff) := by
  have hlt: 2 < ff := by decide
  sorry

#check (inferInstance : SubNegMonoid (ZMod ff))

instance IsThisTrue: SubNegMonoid (ZMod ff) :=
  inferInstance


def map_f_to_bv (rs1_val : ZMod ff) : Option (BitVec 8) :=
  let n := (rs1_val.val : Nat)
  if n < 2^8 then
    some (BitVec.ofNat 8 n)
  else
    none

def map_f_to_bv_16 (rs1_val : ZMod ff) : Option (BitVec 16) :=
  let n := (rs1_val.val : Nat)
  if n < 2^16 then
    some (BitVec.ofNat 16 n)
  else
    none

def map_f_to_bv_32 (rs1_val : ZMod ff) : Option (BitVec 32) :=
  let n := (rs1_val.val : Nat)
  if n < 2^32 then
    some (BitVec.ofNat 32 n)
  else
    none

set_option maxHeartbeats 2000000


lemma extract_bv_rel{bf x} : some (bool_to_bv bf) = map_f_to_bv x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#8 else 0#8) = BitVec.ofNat 8 x.val) := by
  unfold map_f_to_bv
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


lemma extract_bv_rel_16{bf x} : some (bool_to_bv_16 bf) = map_f_to_bv_16 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#16 else 0#16) = BitVec.ofNat 16 x.val) := by
  unfold map_f_to_bv_16
  unfold bool_to_bv_16
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


lemma extract_bv_rel_32{bf x} : some (bool_to_bv_32 bf) = map_f_to_bv_32 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#32 else 0#32) = BitVec.ofNat 32 x.val) := by
  unfold map_f_to_bv_32
  unfold bool_to_bv_32
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



lemma ZMod.eq_if_val (a b : ZMod ff) :
  (a = b ) <->  (a.val = b.val) := by
  apply Iff.intro
  intros h
  rw [h]
  intros h
  apply ZMod.val_injective at h
  exact h


lemma BitVec.ofNat_eq_iff {x y : ℕ} (hx : x < 2^8) (hy : y < 2^8) :
  (x = y)  <-> (BitVec.ofNat 8 x = BitVec.ofNat 8 y):= by
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

lemma BitVec.ofNat_eq_iff_16 {x y : ℕ} (hx : x < 2^16) (hy : y < 2^16) :
  (x = y)  <-> (BitVec.ofNat 16 x = BitVec.ofNat 16 y):= by
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


lemma BitVec.ofNat_eq_iff_32 {x y : ℕ} (hx : x < 2^32) (hy : y < 2^32) :
  (x = y)  <-> (BitVec.ofNat 32 x = BitVec.ofNat 32 y):= by
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


syntax (name := SolveMLE) "solveMLE " : tactic

partial def introAll (i : Nat := 0) : TacticM Unit := do
  let g ← getMainGoal
  let (_, g') ← g.intro (Name.mkSimple s!"h{i}")  -- note the ← bind in a do-block
  replaceMainGoal [g']                              -- OK: statement inside do

private def termFor (nm : Name) : TacticM (TSyntax `term) := withMainContext do
  match (← getLCtx).findFromUserName? nm with
  | some d => pure ⟨(mkIdent d.userName).raw⟩
  | none   => pure ⟨(mkIdent nm).raw⟩


def XOR_16 [Field f] : Subtable f 16 :=
 subtableFromMLE (fun x => 0 + 1*((1 - x[7])*x[15] + x[7]*(1 - x[15])) + 2*((1 - x[6])*x[14] + x[6]*(1 - x[14])) + 4*((1 - x[5])*x[13] + x[5]*(1 - x[13])) + 8*((1 - x[4])*x[12] + x[4]*(1 - x[12])) + 16*((1 - x[3])*x[11] + x[3]*(1 - x[11])) + 32*((1 - x[2])*x[10] + x[2]*(1 - x[10])) + 64*((1 - x[1])*x[9] + x[1]*(1 - x[9])) + 128*((1 - x[0])*x[8] + x[0]*(1 - x[8])))


elab_rules : tactic
| `(tactic| solveMLE) => do
  let mut newHyp := true
  let mut index := 0
  let mut hyps : List Name := []
  let mut ids : List (TSyntax `ident) := []
  while newHyp do
    try
      introAll index
      hyps := hyps ++ [Name.mkSimple s!"h{index}"]
      index := index +1
    catch _ => newHyp := false
   match hyps with
  | [] => pure ()
  | first :: rest => do
      let _firstId : TSyntax `ident := mkIdent first
      -- do stuff that needs `first` if you like

      -- iterate over the tail
      index := 0
      let g ← getMainGoal
      for x in rest do
        index := index +1
        --  let some decl := (← getLCtx).findFromUserName? x
        --   | pure ()
        let id : TSyntax `ident ← g.withContext do
          let lctx ← getLCtx
          let some decl := lctx.findFromUserName? x
               | throwError m!"no hyp `{x}`"
          pure (mkIdent decl.userName)

        evalTactic (← `(tactic| rw [extract_bv_rel] at $id:ident))
        let n1 := Name.mkSimple s!"{x}_1"
        let n2 := Name.mkSimple s!"{x}_2"
        let id1 : TSyntax `ident := mkIdent n1
        let id2 : TSyntax `ident := mkIdent n2
        ids := ids ++ [id1]
        evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩))
      let id : TSyntax `ident ← g.withContext do
          let lctx ← getLCtx
          let some decl := lctx.findFromUserName? hyps[0]!
               | throwError m!"no hyp"
          pure (mkIdent decl.userName)
      -- TODO: THIS IS NOT GOOD NEEDS TO DETECT WHAT TYPE OF BITVECTORS WE ARE TALKING
      evalTactic (← `(tactic| unfold map_f_to_bv at $id:ident; simp at $id:ident))
      let n1 := Name.mkSimple s!"h_1"
      let n2 := Name.mkSimple s!"h_2"
      let id1 : TSyntax `ident := mkIdent n1
      let id2 : TSyntax `ident := mkIdent n2
      evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩; rw [ZMod.eq_if_val]
     -- TODO: TABLE NAME SHOULD BE A PARAMETER
      ; unfold XOR_16
      ; unfold evalSubtable
      ; simp
      ; unfold subtableFromMLE
      ; simp
      ; unfold Vector.append
      ; simp ))
      let idsArr : Array (TSyntax `ident) := ids.toArray
      evalTactic (← `(tactic| valify [$[$idsArr:ident],*]))
      evalTactic (← `(tactic| simp;  rw [Nat.mod_eq_of_lt];
      -- TODO: THIS IS NOT GOOD NEEDS TO DETECT WHAT TYPE OF BITVECTORS WE ARE TALKING
      rw [BitVec.ofNat_eq_iff] ))
      let fv1T : TSyntax `term := (← termFor `fv1)
      let fv2T : TSyntax `term := (← termFor `fv2)
      let foT  : TSyntax `term := (← termFor `foutput)
      evalTactic (← `(tactic| bvify [$[$idsArr:ident],*]))
      evalTactic (← `(tactic|
        set a   := ($foT).val ;
        set b10 := ZMod.val ($fv1T)[0] ;
        set b11 := ZMod.val ($fv1T)[1] ;
        set b12 := ZMod.val ($fv1T)[2] ;
        set b13 := ZMod.val ($fv1T)[3] ;
        set b14 := ZMod.val ($fv1T)[4] ;
        set b15 := ZMod.val ($fv1T)[5];
        set b16 := ZMod.val ($fv1T)[6] ;
        set b17 := ZMod.val ($fv1T)[7] ;
        set b20 := ZMod.val ($fv2T)[0] ;
        set b21 := ZMod.val ($fv2T)[1] ;
        set b22 := ZMod.val ($fv2T)[2] ;
        set b23 := ZMod.val ($fv2T)[3] ;
        set b24 := ZMod.val ($fv2T)[4] ;
        set b25 := ZMod.val ($fv2T)[5] ;
        set b26 := ZMod.val ($fv2T)[6] ;
        set b27 := ZMod.val ($fv2T)[7] ;
        bv_decide ;
        exact $id1:ident ;
        ))
      evalTactic (← `(tactic| try_apply_lemma_hyps [$[$idsArr:ident],*]))
  -- use x




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
  solveMLE
