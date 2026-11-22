import EvenP17RecoverAnchorLoad
import CharpolyExecSetup

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 22000

namespace EvenTI.P17Recover

open EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.P12Compare
open EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPLayout20261007 (MatBlock)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar NoVar)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
  (commands commands_run install installed_slots)
open Mathproof.Problem17CharpolyExec

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def charpolyBindings : List (String × Expr) :=
  [(setupInput,.var loadBase),(setupExp,.sub (.var liveAnchorWidth) (.lit 1))]

noncomputable def selectedAnchorCharpoly (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) : Com :=
  .seq (loadSelectedAnchor D F right) (.seq (commands charpolyBindings) fromBank)

private theorem bindingSafe :
    ∀ p ∈ charpolyBindings, ∀ q ∈ charpolyBindings, NoVar p.1 q.2 := by
  intro p hp q hq
  simp only [charpolyBindings,List.mem_cons,List.not_mem_nil,or_false] at hp hq
  rcases hp with rfl|rfl <;> rcases hq with rfl|rfl <;>
    simp [NoVar,setupInput,setupExp,loadBase,liveAnchorWidth]

/-- The selected serialized anchor reaches the checked arbitrary-characteristic
characteristic-polynomial program with its ABI built from the live width. -/
theorem selectedAnchorCharpoly_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) {B S base h cb width tb : ℕ} {s : Env}
    (A : Matrix (Fin (h+1)) (Fin (h+1)) K) (hA : anchors.get i=⟨h+1,A⟩)
    (hSec : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms s)
    (hiB : i.val < B) (hI : s.vars anchorWanted=i.val)
    (hS : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B) (hB : 1 < B)
    (hLen : z.length < B) (hBank : s.arrs "data"=sentinelWords z)
    (hBase : s.vars loadBase=base) (hCoeff : s.vars setupCoeff=cb)
    (hWidth : s.vars setupWidth=width) (hScratch : s.vars setupScratch=tb)
    (hLayout : (contiguous h base cb width tb).valid S B) :
    ∃ t, Run B (selectedAnchorCharpoly D F right) s t
      ((19*i.val+22+(3+(11+encodedBankLoadCost F contiguousAddress ((h+1)*(h+1)))))+
        (7+fromBankCost F h width)) ∧
      Slots F canonical qN.WS S B t ∧ CoeffSlots F t width cb A.charpoly ∧ Frame (selectedAnchorCharpoly D F right) s t := by
  have hFit : base+(h+1)*(h+1) ≤ S := by
    obtain ⟨_,h₁,_,_,_,_,_,_,h₂,_,_⟩ := hLayout
    change base+(h+1)*(h+1) ≤ tb at h₁
    change address h tb 5+5 ≤ S at h₂
    unfold address at h₂
    omega
  obtain ⟨u,ru,hu,hN,hData,_,_,_,_,hKeep⟩ := loadSelectedAnchor_run D F z forms right anchors i
    hSec hiB hI hS hQ hB hLen hBank hBase (by rw [hA]; exact hFit)
  simp only [hA] at hN ru
  let installed (I : NumberedAnchor K) :=
    ∀ k : Fin (I.width*I.width), val F canonical qN.WS u (base+k.val) =
      I.matrix (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hInstalled : installed (anchors.get i) := hData
  have hMatrix : installed ⟨h+1,A⟩ := hA ▸ hInstalled
  have hBaseU := (hKeep loadBase (by decide) (by decide) (by decide) (by decide)
    (by cases right <;> decide)).trans hBase
  have hB0 : base<B := (Nat.le_trans (Nat.le_add_right _ _) hFit).trans_lt hS.slots_word
  have hB1 : h+1<B := by
    have hSq := Nat.le_mul_self (h+1)
    have hSlots := hS.slots_word
    omega
  have ei : (Expr.var loadBase).evalB B u=some base := evalB_var_iff.mpr ⟨hBaseU.symm,hBaseU ▸ hB0⟩
  have ew : (Expr.var liveAnchorWidth).evalB B u=some (h+1) :=
    evalB_var_iff.mpr ⟨hN.symm,hN ▸ hB1⟩
  have ee : (Expr.sub (.var liveAnchorWidth) (.lit 1)).evalB B u=some h := by
    have he := evalB_bin (op:=.sub) ew (evalB_lit hB) (by change (h+1)-1<B; omega)
    simpa using he
  let args := [(setupInput,base),(setupExp,h)]
  let v := install args u
  have rv : Run B (commands charpolyBindings) u v 7 :=
    commands_run charpolyBindings [base,h] u (by rfl) (.cons ei (.cons ee .nil)) bindingSafe
  have hv : Slots F canonical qN.WS S B v := by
    apply installed_slots F args u hu
    intro p hp
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> simp only [Prod.fst] <;> decide
  have hM : MatBlock F v base A := by
    intro j k
    let idx : Fin ((h+1)*(h+1)) := finProdFinEquiv (j,k)
    have idxEq : idx.val=j.val*(h+1)+k.val := by
      simp [idx,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
    change val F canonical qN.WS ((u.setVar setupInput base).setVar setupExp h)
      (base+(j.val*(h+1)+k.val))=A j k
    rw [val_setVar F canonical (by decide : setupExp ≠ qN.WS),
      val_setVar F canonical (by decide : setupInput ≠ qN.WS),← idxEq]
    simpa only [idx,Equiv.symm_apply_apply] using hMatrix idx
  have hCtrl (r : String) (ha : r ≠ setupInput) (hb : r ≠ setupExp)
      (hc : r ≠ liveAnchorWidth) (hd : r ≠ inputBase) (he : r ≠ loadLength)
      (hf : ¬loadChanges r) (hg : r ∉ scalarWrites (selectAnchor right)) :
      v.vars r=s.vars r := by
    simpa [v,args,install,ha,hb] using hKeep r hc hd he hf hg
  obtain ⟨t,rt,ht,hP,_,_⟩ := fromBank_run F A hv hLayout
    (by simp [v,args,install,setupInput,setupExp])
    ((hCtrl _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by cases right <;> decide)).trans hCoeff)
    ((hCtrl _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by cases right <;> decide)).trans hWidth)
    ((hCtrl _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by cases right <;> decide)).trans hScratch)
    (by simp [v,args,install]) hM
  have hr : Run B (selectedAnchorCharpoly D F right) s t _ := ru.seq (rv.seq rt)
  exact ⟨t,hr,ht,hP,Frame.of_run hr⟩

#print axioms selectedAnchorCharpoly_run
end EvenTI.P17Recover
