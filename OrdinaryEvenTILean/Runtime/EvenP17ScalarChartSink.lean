import EvenP15ScalarLoadedMatrix
import EvenP16RecoverChartProduct

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 48000

namespace EvenTI.P17Scalar

open EvenTI.P15Scalar
open EvenTI.Contract
open EvenTI.P16Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots NoVar)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)
open Mathproof.Problem18P34AssemblyMatrixMemory20261003 (matrix_congr)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003
open Mathproof.Problem18IMPMatrixProductLoop20261001 (cost)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private def chartSlot : Expr :=
  .div (.sub (.var triOut) (.var "even.scalar.ws")) (.var canonical.e)

private def chartScalarSetup : List (String × Expr) := [
  (scalarCopySource,chartSlot),(scalarCopyTarget,.lit 0),
  (scalarCopyLength,.mul (.var scalarLoadedDim) (.var scalarLoadedDim))]

noncomputable def chartAndTestScalar (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq triProduct (.seq (commands chartScalarSetup) (loadedMatrixScalar D F "even.scalar.ws"))

/-- Run the paid comparison chart sandwich and test its resulting matrix
directly in the same machine. The square result may be a rectangular crop
product. No separate witness packet needs to be written or read. -/
theorem chartAndTestScalar_run (D : FieldEncoding K) (F : FieldPresentation K)
    {W S a n r k : ℕ} {s : Env}
    (hIn : TriProductInput F W S n r k n s)
    (hOutSlot : s.vars triOut = s.vars "even.scalar.ws"+a*F.e)
    (hFit : a+n*n ≤ S) (hDim : s.vars scalarLoadedDim=n)
    (hQ : Fintype.card K ≤ W) (hP : F.p < W)
    (hLen : (s.arrs "data").length=n*n+1) (hW : n*n+1 < W)
    (hSent : (s.arrs "data").getD (n*n) 0=0) :
    let R := matrix F s (s.vars triLeft) n r *
      (matrix F s (s.vars canonical.aBase) r k * matrix F s (s.vars canonical.bBase) k n)
    ∃ t, Run W (chartAndTestScalar D F) s t
      (cost F.e r k n+cost F.e n r n+installScalarLabelsCost F (n*n)+60*(n*n)+60) ∧
      (t.vars "good"=1 ↔ R = R ⟨0,hIn.height_pos⟩ ⟨0,hIn.height_pos⟩ •
        (1 : Matrix (Fin n) (Fin n) K)) ∧
      t.vars "good" < W ∧ t.inp=s.inp ∧ t.out=s.out := by
  let R := matrix F s (s.vars triLeft) n r *
    (matrix F s (s.vars canonical.aBase) r k * matrix F s (s.vars canonical.bBase) k n)
  have h1 : 1 < W := by omega
  obtain ⟨u,r0,_,hSlots,hProd,hInp,hTape⟩ := triProduct_run F hIn
  have fr := Frame.of_run r0
  have hOutWord : s.vars triOut < W := by
    have hb := hIn.target_output
    have hm := hIn.target_work
    have hL := hIn.first.valid.memory_word
    omega
  have hWBase : s.vars "even.scalar.ws" < W := by omega
  have ha : a < W := by have := hSlots.slots_word; omega
  have hDegree : F.e < W := by
    have hb := hIn.target_output
    have hm := hIn.target_work
    have hL := hIn.first.valid.memory_word
    omega
  have huBase : u.vars "even.scalar.ws" = s.vars "even.scalar.ws" :=
    fr.vars _ (by decide)
  have huOut : u.vars triOut = s.vars triOut := fr.vars _ (by decide)
  have huDim : u.vars scalarLoadedDim = n := (fr.vars _ (by decide)).trans hDim
  have hData : u.arrs "data"=s.arrs "data" := fr.arrs _ (by decide)
  have evO : (Expr.var triOut).evalB W u = some (s.vars triOut) :=
    evalB_var_iff.mpr ⟨huOut.symm,huOut ▸ hOutWord⟩
  have evV : (Expr.var "even.scalar.ws").evalB W u = some (s.vars "even.scalar.ws") :=
    evalB_var_iff.mpr ⟨huBase.symm,huBase ▸ hWBase⟩
  have heq : s.vars triOut-s.vars "even.scalar.ws" = a*F.e := by omega
  have hSub : (Expr.sub (.var triOut) (.var "even.scalar.ws")).evalB W u = some (a*F.e) := by
    rw [←heq]
    exact evalB_bin (op:=.sub) evO evV ((Nat.sub_le _ _).trans_lt hOutWord)
  have evD : (Expr.var canonical.e).evalB W u = some F.e :=
    evalB_var_iff.mpr ⟨hSlots.base.degree.symm,hSlots.base.degree ▸ hDegree⟩
  have evS : chartSlot.evalB W u = some a := by
    have ev := evalB_bin (op:=.div) hSub evD (show (a*F.e)/F.e < W by
      rwa [Nat.mul_div_cancel _ F.degree_pos])
    exact (show chartSlot.evalB W u = _ from ev).trans
      (congrArg some (Nat.mul_div_cancel _ F.degree_pos))
  have evN : (Expr.var scalarLoadedDim).evalB W u = some n :=
    evalB_var_iff.mpr ⟨huDim.symm,huDim ▸ hIn.height_word⟩
  let vals := [a,0,n*n]
  have ev : List.Forall₂ (fun v w => v.2.evalB W u = some w) chartScalarSetup vals := by
    simp only [chartScalarSetup,vals,List.forall₂_cons]
    exact ⟨evS,evalB_lit (by omega),evalB_bin (op:=.mul) evN evN
      (show n*n < W by omega),List.Forall₂.nil⟩
  let binds := List.zip (chartScalarSetup.map Prod.fst) vals
  let v := install binds u
  have r1 : Run W (commands chartScalarSetup) u v 13 := by
    exact commands_run chartScalarSetup vals u rfl ev (by
      intro p hp q hq
      simp only [chartScalarSetup,List.mem_cons,List.not_mem_nil,or_false] at hp hq
      rcases hp with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;>
        simp [NoVar,chartSlot,scalarCopySource,scalarCopyTarget,scalarCopyLength,scalarLoadedDim,
          triOut,canonical])
  have fv := installed_arrays binds u
  have hvSlots : Slots F canonical "even.scalar.ws" S W v := by
    apply installed_slots F binds u hSlots
    intro q hq
    simp only [binds,chartScalarSetup,vals,List.map_cons,List.map_nil,List.zip_cons_cons,List.zip_nil_left,
      List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> simp only [Prod.fst] <;> decide
  have hvWS : v.vars "even.scalar.ws" = s.vars "even.scalar.ws" := by
    rw [installed_scalar binds u "even.scalar.ws" (by
      simp [binds,chartScalarSetup,vals,scalarCopySource,scalarCopyTarget,scalarCopyLength])]
    exact huBase
  have hvN : v.vars scalarLoadedDim=n := by
    rw [installed_scalar binds u scalarLoadedDim (by
      simp [binds,chartScalarSetup,vals,scalarLoadedDim,scalarCopySource,scalarCopyTarget,scalarCopyLength])]
    exact huDim
  have hvMat : matrix F v (v.vars "even.scalar.ws"+a*F.e) n n = R := by
    rw [hvWS,←hOutSlot]
    trans matrix F u (s.vars triOut) n n
    · apply matrix_congr
      intro i hi
      rw [fv.1]
    · exact hProd
  obtain ⟨t,r2,hScalar,hGood,_,hTi,hTo⟩ := loadedMatrixScalar_run D F (s:=v) R hvSlots
    (by decide) hIn.height_pos hQ hP
    (by simp [v,binds,chartScalarSetup,vals,install,scalarCopySource,scalarCopyTarget,scalarCopyLength])
    (by simp [v,binds,chartScalarSetup,vals,install,scalarCopySource,scalarCopyTarget,scalarCopyLength])
    (by simp [v,binds,chartScalarSetup,vals,install,scalarCopySource,scalarCopyTarget,scalarCopyLength])
    hvN (by omega) hvMat (by rw [fv.1,hData,hLen]) hW (by rw [fv.1,hData,hSent])
  have rr : Run W (chartAndTestScalar D F) s t
      (cost F.e r k n+cost F.e n r n+installScalarLabelsCost F (n*n)+60*(n*n)+60) :=
    (r0.seq (r1.seq r2)).mono (by omega)
  exact ⟨t,rr,hScalar,hGood,hTi.trans (fv.2.1.trans hInp),hTo.trans (fv.2.2.trans hTape)⟩

#print axioms chartAndTestScalar_run
end EvenTI.P17Scalar