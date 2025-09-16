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
import ZkLean.def_ff
--import Mathlib.Tactic.Ring
import Std.Tactic.BVDecide
import Mathlib.Tactic.Linarith
--import ZkLean.valify
--import ZkLean.range_analysis
import ZkLean.valify_helper
import ZkLean.bvify
import Auto.Tactic



open Lean Meta Elab Tactic




def bool_to_bv (b: Bool) : (BitVec 8) := if b == true then 1 else 0
--if b == false then 1

def bool_to_bv_16 (b: Bool) : (BitVec 16) := if b == true then 1 else 0
--if b == false then 1

def bool_to_bv_32 (b: Bool) : (BitVec 32) := if b == true then 1 else 0
--if b == false then 1

def bool_to_bv_64 (b: Bool) : (BitVec 64) := if b == true then 1 else 0
--if b == false then 1


def map_f_to_bv_8 (rs1_val : ZMod ff) : Option (BitVec 8) :=
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

def map_f_to_bv_64 (rs1_val : ZMod ff) : Option (BitVec 64) :=
  let n := (rs1_val.val : Nat)
  if n < 2^64 then
    some (BitVec.ofNat 64 n)
  else
    none

set_option maxHeartbeats 2000000


lemma extract_bv_rel_8{bf x} : some (bool_to_bv bf) = map_f_to_bv_8 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#8 else 0#8) = BitVec.ofNat 8 x.val) := by
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


lemma extract_bv_rel_64{bf x} : some (bool_to_bv_64 bf) = map_f_to_bv_64 x <-> (x.val <= 1 /\ (if (bf = true) = true then 1#64 else 0#64) = BitVec.ofNat 64 x.val) := by
  unfold map_f_to_bv_64
  unfold bool_to_bv_64
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



lemma ZMod.eq_if_val (a b : ZMod ff) :
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



syntax (name := SolveMLE) "solveMLE " ident num : tactic

partial def introAll (i : Nat := 0) (revNames : List Name := []) : TacticM (List Name) := do
  let name := Name.mkSimple s!"h{i}"
  let g ← getMainGoal
  try
    let (_, g') ← g.intro name
    replaceMainGoal [g']
  catch _ => return revNames.reverse
  introAll (i + 1) (name :: revNames)

private def termFor (nm : Name) : TacticM (TSyntax `term) := withMainContext do
  match (← getLCtx).findFromUserName? nm with
  | some d => pure ⟨(mkIdent d.userName).raw⟩
  | none   => pure ⟨(mkIdent nm).raw⟩

syntax (name := findModLT) "findModLT " num : tactic

@[tactic findModLT] def evalfindModLT : Tactic := fun stx => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let (fn, args) := ty.getAppFnArgs
   let some n := stx[1].isNatLit?
    | throwError "usage: findModLT <n> (natural number)"
  match fn with
    | ``Iff =>
        let (fn2, args2) := args[args.size -1]!.getAppFnArgs
        match fn2 with
        | ``Eq =>
           let (fn3, args3) := args2[args2.size -1]!.getAppFnArgs
           match fn3 with
           | ``HMod.hMod =>
                let lhs := args3[args3.size - 2]!    -- adjust if your indexing changes
        -- build 2 ^ n as a Nat expression
                let twoPowN : Expr := mkApp2 (mkConst ``Nat.pow) (mkNatLit 2) (mkNatLit n)
                let prop ← mkAppM ``LT.lt #[lhs, twoPowN]
                let pr ← g.withContext do mkFreshExprMVar prop
                let gWithHyp  ← g.assert `Leq prop pr
                --let hyp ← g.withContext do pr.mvarId!.assert `Leq prop pr
                -- let gWithHyp ←  g.assert `Leq prop pr
                setGoals [pr.mvarId!, gWithHyp]
           | _ =>
                let lhs := args2[args2.size - 1]!    -- adjust if your indexing changes
        -- build 2 ^ n as a Nat expression
                let twoPowN : Expr := mkApp2 (mkConst ``Nat.pow) (mkNatLit 2) (mkNatLit n)
                let prop ← mkAppM ``LT.lt #[lhs, twoPowN]
                let pr ← g.withContext do mkFreshExprMVar prop
                let gWithHyp  ← g.assert `Leq prop pr
                setGoals [pr.mvarId!, gWithHyp]
        | _ => pure ()
    | _ => pure ()


set_option maxHeartbeats  20000000000000000000
elab_rules : tactic
| `(tactic| solveMLE $table:ident $N:num ) => do
  let n := N.getNat
  let hyps ← introAll
  let mut ids : List (TSyntax `ident) := []
  let first :: rest := hyps | return ()
  let _firstId : TSyntax `ident := mkIdent first
  let g ← getMainGoal
  for x in rest do
    let id : TSyntax `ident ← g.withContext do
      let lctx ← getLCtx
      let some decl := lctx.findFromUserName? x
           | throwError m!"no hyp `{x}`"
      pure (mkIdent decl.userName)
    try
    -- we might have extra hypothesis that don't need to be rewritten
      let extractLemma:= Name.mkSimple s!"extract_bv_rel_{n}"
      evalTactic (← `(tactic| rw [$(mkIdent extractLemma):ident] at $id:ident))
      let n1 := Name.mkSimple s!"{x}_1"
      let n2 := Name.mkSimple s!"{x}_2"
      let id1 : TSyntax `ident := mkIdent n1
      let id2 : TSyntax `ident := mkIdent n2
      ids := ids ++ [id1]
      evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩))
    catch _ => pure ()
  let id : TSyntax `ident ← g.withContext do
      let lctx ← getLCtx
      let some decl := lctx.findFromUserName? hyps[0]!
           | throwError m!"no hyp"
      pure (mkIdent decl.userName)
  let map_f :=  Name.mkSimple s!"map_f_to_bv_{n}"
  evalTactic (← `(tactic| unfold $(mkIdent map_f):ident at $id:ident; simp at $id:ident))
  let n1 := Name.mkSimple s!"h_1"
  let n2 := Name.mkSimple s!"h_2"
  let id1 : TSyntax `ident := mkIdent n1
  let id2 : TSyntax `ident := mkIdent n2
  evalTactic (← `(tactic| rcases $id:ident with ⟨$id1:ident, $id2:ident⟩; rw [ZMod.eq_if_val]
  ; unfold $table:ident
  ; unfold evalSubtable
  ; simp (config := { failIfUnchanged := false })
  ; unfold subtableFromMLE
  ; simp (config := { failIfUnchanged := false })
  ; unfold Vector.append
  ; simp (config := { failIfUnchanged := false })))
  let idsArr : Array (TSyntax `ident) := ids.toArray
  --let i <- getMainGoal
  --logInfo m!"{ids}"

  -- TODO: I don't like this but otherwise we cant solve sign extend (maybe this should also be passed in as a parameter)
  evalTactic (← `(tactic| try valify [$[$idsArr:ident],*]))
  let g ← getMainGoal
  let gt <- g.getType
  let ty ← instantiateMVars (← g.getType)
  let t' ← firstCompositeInsideVal? ty
  let mut valhelp := false
  match t' with
  | some t =>
    valhelp := true
    evalTactic (← `(tactic| valify_helper [$[$idsArr:ident],*]))
    evalTactic (← `(tactic| intro NatLeq; intro ZLeq; intro Eq; simp at Eq ; rw [Eq] ; valify [$[$idsArr:ident],*]))
  | none  => pure ()
  evalTactic (← `(tactic| try simp )) -- rw [Nat.mod_eq_of_lt]))
  let nSyntax : TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString n)⟩
  evalTactic (← `(tactic| findModLT $nSyntax) )
  -- -- let g <- getMainGoal
  -- -- logInfo m!"Hello?{g}"
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| try_apply_lemma_hyps [$[$idsArr:ident],*]))
  if valhelp then
       evalTactic (← `(tactic|
       simp [<- Nat.lt_add_one_iff];
       simp [Nat.mul_assoc] at NatLeq;
       apply NatLeq;
       ))
  evalTactic (← `(tactic| try simp))

  evalTactic (← `(tactic| intro Leq))
  evalTactic (← `(tactic| try rw [Nat.mod_eq_of_lt]))
  let lemmaName := Name.mkSimple s!"BitVec_ofNat_eq_iff_{n}"
  evalTactic (← `(tactic| rw [$(mkIdent lemmaName):ident]))



-- --   -- TODO : Should fv1 should be passed in as parameters?
  let fv1T : TSyntax `term := (← termFor `fv1)
  let fv2T : TSyntax `term := (← termFor `fv2)
  let foT  : TSyntax `term := (← termFor `foutput)
  if valhelp then
   evalTactic (← `(tactic| simp [Nat.lt_succ_iff] at NatLeq))
   evalTactic (← `(tactic| simp [Nat.mul_assoc] at NatLeq))
   evalTactic (← `(tactic| try bvify [NatLeq]))
   evalTactic (← `(tactic| try bvify [$[$idsArr:ident],*]))
   evalTactic (← `(tactic| clear NatLeq; clear ZLeq; clear Eq))
  else
     evalTactic (← `(tactic| try bvify [$[$idsArr:ident],*]))
  evalTactic (← `(tactic| try unfold bool_to_bv))
  evalTactic (← `(tactic| try unfold bool_to_bv_32))
  evalTactic (← `(tactic| clear Leq))
  -- -- TODO: I don't the number bits should be hardcoded like this
  evalTactic (← `(tactic|set a   := ($foT).val))
  let mut index := 0
  while index < ids.length/2 do
    -- names for the bound and its equality
    let idName  := Name.mkSimple s!"b0_{index}"

    -- identifiers/syntax nodes
    let idSyn   : TSyntax `ident := mkIdent idName
    let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

    -- safest access: .get! (parses reliably inside quotations)
    evalTactic (← `(tactic|
      set $idSyn := $fv1T[$idxSyn]
    ))
    index := index + 1
  index := 0
  while index < ids.length/2 do
    -- names for the bound and its equality
    let idName  := Name.mkSimple s!"b1_{index}"

    -- identifiers/syntax nodes
    let idSyn   : TSyntax `ident := mkIdent idName
    let idxSyn  : TSyntax `term  := Syntax.mkNumLit (toString index)

    -- safest access: .get! (parses reliably inside quotations)
    evalTactic (← `(tactic|
      set $idSyn := $fv2T[$idxSyn]
    ))
    index := index + 1

-- -- --     -- set b10 := ZMod.val ($fv1T)[0] ;
-- -- --     -- set b11 := ZMod.val ($fv1T)[1] ;
-- -- --     -- set b12 := ZMod.val ($fv1T)[2] ;
-- -- --     -- set b13 := ZMod.val ($fv1T)[3] ;
-- -- --     -- set b14 := ZMod.val ($fv1T)[4] ;
-- -- --     -- set b15 := ZMod.val ($fv1T)[5];
-- -- --     -- set b16 := ZMod.val ($fv1T)[6] ;
-- -- --     -- set b17 := ZMod.val ($fv1T)[7] ;
-- -- --     -- set b20 := ZMod.val ($fv2T)[0] ;
-- -- --     -- set b21 := ZMod.val ($fv2T)[1] ;
-- -- --     -- set b22 := ZMod.val ($fv2T)[2] ;
-- -- --     -- set b23 := ZMod.val ($fv2T)[3] ;
-- -- --     -- set b24 := ZMod.val ($fv2T)[4] ;
-- -- --     -- set b25 := ZMod.val ($fv2T)[5] ;
-- -- --     -- set b26 := ZMod.val ($fv2T)[6] ;
-- -- --     -- set b27 := ZMod.val ($fv2T)[7] ;
-- -- --   let g <- getMainGoal
-- -- --   evalTactic (← `(tactic| bv_normalize))
-- -- --   let h <- getMainGoal
-- -- --   --logInfo m!"started bv_decice"
  evalTactic (← `(tactic| bv_decide (config := {timeout := 300}) ;
    apply $id1:ident ;
    ))
  evalTactic (← `(tactic|  apply Nat.lt_of_lt_of_le;
  apply Leq;
  decide))
  try
    evalTactic (← `(tactic|  apply Nat.lt_of_lt_of_le;
    apply Leq;
    decide))
  catch _ => pure ()
--   evalTactic (← `(tactic|  exact Nat.lt_of_lt_of_le Leq (by decide)))
--   logInfo m!"finished bv_decide :)"
--   evalTactic (← `(tactic| try_apply_lemma_hyps [$[$idsArr:ident],*]))
-- -- --   -- -- use x

-- -- def SRA_SIGN_16 [Field f] : Subtable f 16 :=
-- --  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0] + 8*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0] + 8*x[0] + 4*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0] + 8*x[0] + 4*x[0] + 2*x[0]))

-- -- lemma sra_sign_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
-- --   some bvoutput = map_f_to_bv_32 foutput ->
-- --    some (bool_to_bv_32 bv1[7])  = map_f_to_bv_32 fv1[0]  ->
-- --    some (bool_to_bv_32 bv1[6]) = map_f_to_bv_32 fv1[1]  ->
-- --    some (bool_to_bv_32 bv1[5]) = map_f_to_bv_32 fv1[2]  ->
-- --    some (bool_to_bv_32 bv1[4]) = map_f_to_bv_32 fv1[3]  ->
-- --    some (bool_to_bv_32 bv1[3]) = map_f_to_bv_32 fv1[4]  ->
-- --   some (bool_to_bv_32 bv1[2]) = map_f_to_bv_32 fv1[5]  ->
-- --    some (bool_to_bv_32 bv1[1]) = map_f_to_bv_32 fv1[6]  ->
-- --    some (bool_to_bv_32 bv1[0]) = map_f_to_bv_32 fv1[7]  ->
-- --   some (bool_to_bv_32 bv2[7]) = map_f_to_bv_32 fv2[0]  ->
-- --   some (bool_to_bv_32 bv2[6]) = map_f_to_bv_32 fv2[1]  ->
-- --   some (bool_to_bv_32 bv2[5]) = map_f_to_bv_32 fv2[2]  ->
-- --   some (bool_to_bv_32 bv2[4]) = map_f_to_bv_32 fv2[3]  ->
-- --   some (bool_to_bv_32 bv2[3]) = map_f_to_bv_32 fv2[4]  ->
-- --   some (bool_to_bv_32 bv2[2]) = map_f_to_bv_32 fv2[5]  ->
-- --   some (bool_to_bv_32 bv2[1]) = map_f_to_bv_32 fv2[6]  ->
-- --   some (bool_to_bv_32 bv2[0]) = map_f_to_bv_32 fv2[7]  ->
-- --   bv2[7] = false ->
-- --   bv2[6] = false ->
-- --   bv2[5] = false ->
-- --   (bvoutput =(BitVec.sshiftRight (bv1.signExtend 32) 31)    -- 0xFFFF_FFFF if sign=1 else 0
-- --   &&& (~~~ ((BitVec.ofNat 32 0xFFFF_FFFF) >>> bv2.toNat)))

-- --   =
-- --   (foutput = evalSubtable SRA_SIGN_16 (Vector.append fv1 fv2))
-- --  := by
-- --     solveMLE SRA_SIGN_16 32


-- --def XOR_16 [Field f] : Subtable f 16 :=
--  --subtableFromMLE (fun x => 0 + 1*((1 - x[7])*x[15] + x[7]*(1 - x[15])) + 2*((1 - x[6])*x[14] + x[6]*(1 - x[14])) + 4*((1 - x[5])*x[13] + x[5]*(1 - x[13])) + 8*((1 - x[4])*x[12] + x[4]*(1 - x[12])) + 16*((1 - x[3])*x[11] + x[3]*(1 - x[11])) + 32*((1 - x[2])*x[10] + x[2]*(1 - x[10])) + 64*((1 - x[1])*x[9] + x[1]*(1 - x[9])) + 128*((1 - x[0])*x[8] + x[0]*(1 - x[8])))

-- --  lemma xor_mle_one_chunk_liza[ZKField f] (bv1 bv2 : BitVec 8) (fv1 fv2 : Vector f 8) :
-- --   some bvoutput = map_f_to_bv_8 foutput ->
-- --    some (bool_to_bv bv1[7])  = map_f_to_bv_8 fv1[0]  ->
-- --    some (bool_to_bv bv1[6]) = map_f_to_bv_8 fv1[1]  ->
-- --    some (bool_to_bv bv1[5]) = map_f_to_bv_8 fv1[2]  ->
-- --    some (bool_to_bv bv1[4]) = map_f_to_bv_8 fv1[3]  ->
-- --    some (bool_to_bv bv1[3]) = map_f_to_bv_8 fv1[4]  ->
-- --    some (bool_to_bv bv1[2]) = map_f_to_bv_8 fv1[5]  ->
-- --    some (bool_to_bv bv1[1]) = map_f_to_bv_8 fv1[6]  ->
-- --    some (bool_to_bv bv1[0]) = map_f_to_bv_8 fv1[7]  ->
-- --   some (bool_to_bv bv2[7]) = map_f_to_bv_8 fv2[0]  ->
-- --   some (bool_to_bv bv2[6]) = map_f_to_bv_8 fv2[1]  ->
-- --   some (bool_to_bv bv2[5]) = map_f_to_bv_8 fv2[2]  ->
-- --   some (bool_to_bv bv2[4]) = map_f_to_bv_8 fv2[3]  ->
-- --   some (bool_to_bv bv2[3]) = map_f_to_bv_8 fv2[4]  ->
-- --   some (bool_to_bv bv2[2]) = map_f_to_bv_8 fv2[5]  ->
-- --   some (bool_to_bv bv2[1]) = map_f_to_bv_8 fv2[6]  ->
-- --   some (bool_to_bv bv2[0]) = map_f_to_bv_8 fv2[7]  ->
-- --   (bvoutput = BitVec.xor bv1 bv2)
-- --   =
-- --   (foutput = evalSubtable XOR_16 (Vector.append fv1 fv2))
-- -- := by
-- --   solveMLE XOR_16 8

theorem test (x y : f)
  (hx : x.val ≤ 1) (hy : y.val <= 1)
   : (1-x).val = 123 := by
  valify [hx, hy]
  sorry
  --simp [one_val hx] at h
  --apply ZMod.val_sub at h
